package ircevent

// Hermetic tests for SCRAM-SHA-256 SASL support. These tests do not
// require a live ircd: they drive Connection.Connect() against an
// in-process mock IRC server that implements the SCRAM-SHA-256
// exchange independently.

import (
	"bufio"
	"bytes"
	"crypto/hmac"
	"crypto/rand"
	"crypto/sha256"
	"encoding/base64"
	"encoding/hex"
	"fmt"
	"io/ioutil"
	"log"
	"net"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/ergochat/irc-go/ircmsg"
	"github.com/ergochat/irc-go/ircutils"
)

const (
	scramTestNick     = "scramtest"
	scramTestLogin    = "scramuser"
	scramTestPassword = "scram-passphrase-do-not-leak"
	scramServerName   = "mock.server"
)

// --- independent SCRAM-SHA-256 server-side helpers (test only) ---

func testPBKDF2SHA256(password, salt []byte, iterations, keyLength int) []byte {
	hashLength := sha256.Size
	numBlocks := (keyLength + hashLength - 1) / hashLength
	result := make([]byte, 0, numBlocks*hashLength)
	for block := 1; block <= numBlocks; block++ {
		mac := hmac.New(sha256.New, password)
		mac.Write(salt)
		mac.Write([]byte{byte(block >> 24), byte(block >> 16), byte(block >> 8), byte(block)})
		u := mac.Sum(nil)
		derived := make([]byte, len(u))
		copy(derived, u)
		for i := 1; i < iterations; i++ {
			mac = hmac.New(sha256.New, password)
			mac.Write(u)
			u = mac.Sum(nil)
			for j := range derived {
				derived[j] ^= u[j]
			}
		}
		result = append(result, derived...)
	}
	return result[:keyLength]
}

func testHMAC(key []byte, message string) []byte {
	mac := hmac.New(sha256.New, key)
	mac.Write([]byte(message))
	return mac.Sum(nil)
}

func testSHA256(data []byte) []byte {
	sum := sha256.Sum256(data)
	return sum[:]
}

// --- mock IRC server ---

type scramMockConfig struct {
	password string
	salt     []byte
	// iterations advertised in server-first
	iterations int
	// mech the server expects
	mech string
	// malformedServerFirst, when non-empty, replaces the server-first
	// message entirely (used for protocol error tests)
	malformedServerFirst func(clientNonce string) string
	// badSignature makes the server-final carry a wrong signature
	badSignature bool
	// serverAbort makes the server answer AUTHENTICATE <mech> with
	// AUTHENTICATE * instead of the empty challenge
	serverAbort bool
	// largeMessages tunes the salt so the base64 server-first message
	// splits into 400-byte chunks, with the final chunk exactly 400
	// bytes (followed by the terminating '+')
	largeMessages bool
	// hangUp closes the connection once registration completes,
	// exercising automatic reconnection
	hangUp bool
	// send904 replies 904 after the client aborts with AUTHENTICATE *
	// (and still completes registration when the client treats SASL
	// as optional)
	send904 bool
}

type scramMockConn struct {
	registered chan struct{}
	aborted    chan struct{} // closed when the client sends AUTHENTICATE *

	clientNonce        string
	escapedUsername    string
	sentAbort          bool // client sent AUTHENTICATE *
	sentEmptyResponse  bool // client sent the completion AUTHENTICATE +
	capEndReceived     bool // client sent CAP END
	capEndAfterSuccess bool // CAP END arrived after the server sent 903
	registrationDone   bool
	chunkTooLong       bool // some outgoing AUTHENTICATE chunk exceeded 400 bytes
	largestChunkCount  int  // most AUTHENTICATE chunks used for one message
	sentTerminator     bool // server sent a trailing '+' after an exact 400-byte chunk
	mech               string
}

type scramMockServer struct {
	t        *testing.T
	listener net.Listener
	config   scramMockConfig

	mu       sync.Mutex
	conns    []*scramMockConn
	closed   bool
	closedCh chan struct{}
}

func newSCRAMMockServer(t *testing.T, config scramMockConfig) *scramMockServer {
	if config.password == "" {
		config.password = scramTestPassword
	}
	if config.mech == "" {
		config.mech = scramMech
	}
	if config.iterations == 0 {
		config.iterations = 4096
	}
	if config.salt == nil {
		config.salt = []byte("unit-test-salt-0123456789")
	}
	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("could not listen: %v", err)
	}
	server := &scramMockServer{
		t:        t,
		listener: listener,
		config:   config,
		closedCh: make(chan struct{}),
	}
	go server.acceptLoop()
	t.Cleanup(server.close)
	return server
}

func (s *scramMockServer) addr() string {
	return s.listener.Addr().String()
}

func (s *scramMockServer) acceptLoop() {
	for {
		conn, err := s.listener.Accept()
		if err != nil {
			return
		}
		mc := &scramMockConn{
			registered: make(chan struct{}),
			aborted:    make(chan struct{}),
		}
		s.mu.Lock()
		if s.closed {
			s.mu.Unlock()
			conn.Close()
			return
		}
		connIndex := len(s.conns)
		s.conns = append(s.conns, mc)
		s.mu.Unlock()
		go s.handleConn(conn, mc, connIndex)
	}
}

func (s *scramMockServer) close() {
	s.mu.Lock()
	if s.closed {
		s.mu.Unlock()
		return
	}
	s.closed = true
	s.mu.Unlock()
	s.listener.Close()
	close(s.closedCh)
}

func (s *scramMockServer) connCount() int {
	s.mu.Lock()
	defer s.mu.Unlock()
	return len(s.conns)
}

func (s *scramMockServer) firstConn() *scramMockConn {
	s.mu.Lock()
	defer s.mu.Unlock()
	if len(s.conns) == 0 {
		return nil
	}
	return s.conns[0]
}

func (s *scramMockServer) waitForConnCount(t *testing.T, count int) {
	deadline := time.Now().Add(10 * time.Second)
	for time.Now().Before(deadline) {
		if s.connCount() >= count {
			return
		}
		time.Sleep(5 * time.Millisecond)
	}
	t.Fatalf("timed out waiting for %d connections, got %d", count, s.connCount())
}

func (s *scramMockServer) writeLine(conn net.Conn, line string) {
	if _, err := fmt.Fprintf(conn, "%s\r\n", line); err != nil {
		s.t.Logf("mock server write failed: %v", err)
	}
}

// sendSASLMessage sends a raw SCRAM message following the IRCv3
// AUTHENTICATE chunking rules.
func (s *scramMockServer) sendSASLMessage(conn net.Conn, mc *scramMockConn, raw []byte) {
	chunks := ircutils.EncodeSASLResponse(raw)
	if len(chunks) > mc.largestChunkCount {
		mc.largestChunkCount = len(chunks)
	}
	// a trailing '+' on a multi-chunk message means the final data
	// chunk was exactly 400 bytes long
	if len(chunks) > 1 && chunks[len(chunks)-1] == "+" {
		mc.sentTerminator = true
	}
	for _, chunk := range chunks {
		if len(chunk) > 400 {
			s.t.Errorf("mock server produced an oversized chunk: %d", len(chunk))
		}
		s.writeLine(conn, "AUTHENTICATE "+chunk)
	}
}

func (s *scramMockServer) sendRegistration(conn net.Conn, mc *scramMockConn, connIndex int) {
	s.writeLine(conn, fmt.Sprintf(":%s 001 %s :Welcome to the mock network", scramServerName, scramTestNick))
	s.writeLine(conn, fmt.Sprintf(":%s 005 %s CHANTYPES=# :are supported by this server", scramServerName, scramTestNick))
	s.writeLine(conn, fmt.Sprintf(":%s 422 %s :MOTD File is missing", scramServerName, scramTestNick))
	mc.registrationDone = true
	close(mc.registered)
	// only the first connection is torn down, so the client reconnects
	// exactly once instead of looping forever
	if s.config.hangUp && connIndex == 0 {
		conn.Close()
	}
}

func (s *scramMockServer) handleConn(conn net.Conn, mc *scramMockConn, connIndex int) {
	defer conn.Close()
	reader := bufio.NewReader(conn)
	var saslBuffer *ircutils.SASLBuffer
	scramStage := 0 // 0: expecting client-first, 1: expecting client-final
	saslActive := false
	sentSuccess := false

	// SCRAM server-side state
	var clientFirstBare, serverFirstText, fullNonce string
	var storedKey, serverKey []byte

	for {
		line, err := reader.ReadString('\n')
		if err != nil {
			return
		}
		line = strings.TrimRight(strings.TrimRight(line, "\n"), "\r")
		if line == "" {
			continue
		}
		msg, err := ircmsg.ParseLine(line)
		if err != nil {
			s.t.Logf("mock server could not parse %q: %v", line, err)
			continue
		}

		switch msg.Command {
		case "CAP":
			if len(msg.Params) < 1 {
				continue
			}
			switch msg.Params[0] {
			case "LS":
				s.writeLine(conn, fmt.Sprintf(":%s CAP %s LS :sasl", scramServerName, scramTestNick))
			case "REQ":
				s.writeLine(conn, fmt.Sprintf(":%s CAP %s ACK :%s", scramServerName, scramTestNick, msg.Params[1]))
			case "END":
				mc.capEndReceived = true
				if sentSuccess {
					mc.capEndAfterSuccess = true
				}
				if mc.registrationDone {
					continue
				}
				s.sendRegistration(conn, mc, connIndex)
			}
		case "NICK", "USER", "PASS", "WEBIRC":
			// registration preamble, ignored
		case "PING":
			s.writeLine(conn, "PONG "+lastParam(&msg))
		case "QUIT":
			return
		case "AUTHENTICATE":
			if len(msg.Params) == 0 {
				continue
			}
			param := msg.Params[0]
			if len(param) > 400 {
				mc.chunkTooLong = true
			}

			// mechanism selection
			if param == s.config.mech {
				mc.mech = param
				saslActive = true
				if s.config.serverAbort {
					s.writeLine(conn, "AUTHENTICATE *")
				} else {
					s.writeLine(conn, "AUTHENTICATE +")
				}
				if s.config.mech == scramMech {
					saslBuffer = ircutils.NewSASLBuffer(0)
				}
				continue
			}

			if !saslActive {
				continue
			}

			// client-side abort
			if param == "*" {
				mc.sentAbort = true
				close(mc.aborted)
				if s.config.send904 {
					s.writeLine(conn, fmt.Sprintf(":%s 904 %s :SASL authentication failed", scramServerName, scramTestNick))
					// let the client continue with CAP END registration
				}
				continue
			}

			// one-shot mechanisms
			if s.config.mech == "PLAIN" {
				raw := s.decodeSASL(s.t, param)
				expected := bytes.Join([][]byte{
					[]byte(scramTestLogin), []byte(scramTestLogin), []byte(scramTestPassword),
				}, []byte{0})
				if !bytes.Equal(raw, expected) {
					s.writeLine(conn, fmt.Sprintf(":%s 904 %s :SASL authentication failed", scramServerName, scramTestNick))
					continue
				}
				sentSuccess = true
				s.writeLine(conn, fmt.Sprintf(":%s 903 %s :SASL authentication successful", scramServerName, scramTestNick))
				continue
			}
			if s.config.mech == "EXTERNAL" {
				if param != "+" {
					s.writeLine(conn, fmt.Sprintf(":%s 904 %s :SASL authentication failed", scramServerName, scramTestNick))
					continue
				}
				sentSuccess = true
				s.writeLine(conn, fmt.Sprintf(":%s 903 %s :SASL authentication successful", scramServerName, scramTestNick))
				continue
			}

			// SCRAM-SHA-256: reassemble chunks
			if param == "+" && scramStage == 1 {
				// completion message after a verified server-final
				mc.sentEmptyResponse = true
				sentSuccess = true
				s.writeLine(conn, fmt.Sprintf(":%s 903 %s :SASL authentication successful", scramServerName, scramTestNick))
				continue
			}
			done, raw, err := saslBuffer.Add(param)
			if err != nil {
				s.t.Logf("mock server SASL buffer error: %v", err)
				return
			}
			if !done {
				continue
			}

			if scramStage == 0 {
				scramStage = 1
				clientFirst := string(raw)
				if !strings.HasPrefix(clientFirst, scramGS2Header) {
					s.t.Errorf("unexpected GS2 header in client-first: %q", clientFirst)
				}
				clientFirstBare = strings.TrimPrefix(clientFirst, scramGS2Header)
				attrs, err := parseSCRAMAttributes(clientFirstBare)
				if err != nil {
					s.t.Errorf("bad client-first attributes: %v", err)
					return
				}
				username, _ := scramAttributeValue(attrs, 'n')
				mc.escapedUsername = username
				clientNonce, ok := scramAttributeValue(attrs, 'r')
				if !ok {
					s.t.Error("client-first missing nonce")
					return
				}
				mc.clientNonce = clientNonce

				if s.config.malformedServerFirst != nil {
					s.sendSASLMessage(conn, mc, []byte(s.config.malformedServerFirst(clientNonce)))
					continue
				}

				fullNonce = clientNonce + "srv-" + s.randomSuffix()
				salt := s.config.salt
				if s.config.largeMessages {
					salt = s.tuneSaltForExactBoundary(fullNonce)
				}
				serverFirstText = fmt.Sprintf("r=%s,s=%s,i=%d",
					fullNonce, base64.StdEncoding.EncodeToString(salt), s.config.iterations)

				saltedPassword := testPBKDF2SHA256([]byte(s.config.password), salt, s.config.iterations, sha256.Size)
				clientKey := testHMAC(saltedPassword, "Client Key")
				storedKey = testSHA256(clientKey)
				serverKey = testHMAC(saltedPassword, "Server Key")

				s.sendSASLMessage(conn, mc, []byte(serverFirstText))
				continue
			}

			// client-final
			clientFinal := string(raw)
			proofIndex := strings.LastIndex(clientFinal, ",p=")
			if proofIndex == -1 {
				s.t.Error("client-final missing proof")
				return
			}
			clientFinalNoProof := clientFinal[:proofIndex]
			proofEncoded := clientFinal[proofIndex+3:]
			attrs, err := parseSCRAMAttributes(clientFinalNoProof)
			if err != nil {
				s.t.Errorf("bad client-final attributes: %v", err)
				return
			}
			nonce, _ := scramAttributeValue(attrs, 'r')
			if nonce != fullNonce {
				s.t.Errorf("client-final nonce %q does not match %q", nonce, fullNonce)
				return
			}
			channelBinding, _ := scramAttributeValue(attrs, 'c')
			if channelBinding != "biws" {
				s.t.Errorf("unexpected channel binding %q", channelBinding)
			}
			proof, err := base64.StdEncoding.DecodeString(proofEncoded)
			if err != nil {
				s.t.Errorf("bad client proof encoding: %v", err)
				return
			}
			authMessage := clientFirstBare + "," + serverFirstText + "," + clientFinalNoProof
			clientSignature := testHMAC(storedKey, authMessage)
			recoveredClientKey := xorBytes(proof, clientSignature)
			if !bytes.Equal(testSHA256(recoveredClientKey), storedKey) {
				s.t.Error("client proof verification failed")
				return
			}
			serverSignature := testHMAC(serverKey, authMessage)
			if s.config.badSignature {
				serverSignature = testSHA256(serverSignature)
			}
			s.sendSASLMessage(conn, mc, []byte("v="+base64.StdEncoding.EncodeToString(serverSignature)))
		}
	}
}

func (s *scramMockServer) decodeSASL(t *testing.T, value string) []byte {
	raw, err := base64.StdEncoding.DecodeString(value)
	if err != nil {
		t.Fatalf("mock server could not decode SASL payload: %v", err)
	}
	return raw
}

func (s *scramMockServer) randomSuffix() string {
	buf := make([]byte, 12)
	if _, err := rand.Read(buf); err != nil {
		s.t.Fatalf("random failed: %v", err)
	}
	return base64.RawURLEncoding.EncodeToString(buf)
}

// tuneSaltForExactBoundary grows the salt until the base64-encoded
// server-first message has a length divisible by 400, forcing the
// terminating '+' after an exact 400-byte final chunk.
func (s *scramMockServer) tuneSaltForExactBoundary(nonce string) []byte {
	salt := make([]byte, 1024)
	if _, err := rand.Read(salt); err != nil {
		s.t.Fatalf("random failed: %v", err)
	}
	for {
		text := fmt.Sprintf("r=%s,s=%s,i=%d",
			nonce, base64.StdEncoding.EncodeToString(salt), s.config.iterations)
		encoded := base64.StdEncoding.EncodeToString([]byte(text))
		if len(encoded)%400 == 0 {
			return salt
		}
		salt = append(salt, 0)
	}
}

// --- client construction ---

func scramTestClient(server *scramMockServer, mech, login, password string) *Connection {
	return &Connection{
		Server:        server.addr(),
		Nick:          scramTestNick,
		User:          scramTestNick,
		RealName:      scramTestNick,
		UseSASL:       true,
		SASLLogin:     login,
		SASLPassword:  password,
		SASLMech:      mech,
		Timeout:       10 * time.Second,
		KeepAlive:     30 * time.Second,
		ReconnectFreq: 50 * time.Millisecond,
		Log:           log.New(ioutil.Discard, "", 0),
	}
}

func waitForRegistration(t *testing.T, mc *scramMockConn) {
	t.Helper()
	select {
	case <-mc.registered:
	case <-time.After(10 * time.Second):
		t.Fatal("timed out waiting for mock server registration")
	}
}

func waitForAbort(t *testing.T, mc *scramMockConn) {
	t.Helper()
	select {
	case <-mc.aborted:
	case <-time.After(10 * time.Second):
		t.Fatal("timed out waiting for the client to send AUTHENTICATE *")
	}
}

// --- tests ---

func TestSCRAMHappyPath(t *testing.T) {
	// username containing both characters that require SCRAM escaping
	login := "user=name,with=stuff"
	server := newSCRAMMockServer(t, scramMockConfig{mech: scramMech})
	client := scramTestClient(server, scramMech, login, scramTestPassword)

	if err := client.Connect(); err != nil {
		t.Fatalf("Connect failed: %v", err)
	}
	defer func() {
		client.Quit()
		client.Wait()
	}()

	mc := server.firstConn()
	waitForRegistration(t, mc)

	if mc.clientNonce == "" {
		t.Error("server never observed a client nonce")
	}
	if mc.escapedUsername != "user=3Dname=2Cwith=3Dstuff" {
		t.Errorf("username not escaped correctly: %q", mc.escapedUsername)
	}
	if !mc.sentEmptyResponse {
		t.Error("client did not send the empty AUTHENTICATE + after server-final")
	}
	if mc.sentAbort {
		t.Error("client aborted a successful exchange")
	}
	if !mc.capEndAfterSuccess {
		t.Error("CAP END was not sent after 903 RPL_SASLSUCCESS")
	}
	if mc.chunkTooLong {
		t.Error("client sent an AUTHENTICATE chunk over 400 bytes")
	}
	if mc.largestChunkCount != 1 || mc.sentTerminator {
		t.Error("short SCRAM messages must be sent as a single chunk without a terminator")
	}
	if !mc.registrationDone {
		t.Error("registration never completed")
	}
	if client.State() != ConnectionActive {
		t.Errorf("unexpected connection state: %d", client.State())
	}
}

func TestSCRAMReconnectUsesFreshNonce(t *testing.T) {
	server := newSCRAMMockServer(t, scramMockConfig{mech: scramMech, hangUp: true})
	client := scramTestClient(server, scramMech, scramTestLogin, scramTestPassword)

	if err := client.Connect(); err != nil {
		t.Fatalf("Connect failed: %v", err)
	}
	server.waitForConnCount(t, 2)
	defer func() {
		client.Quit()
		client.Wait()
	}()

	server.mu.Lock()
	conns := append([]*scramMockConn(nil), server.conns...)
	server.mu.Unlock()
	if len(conns) < 2 {
		t.Fatalf("expected at least two connections, got %d", len(conns))
	}
	waitForRegistration(t, conns[0])
	waitForRegistration(t, conns[1])

	if conns[0].clientNonce == "" || conns[1].clientNonce == "" {
		t.Fatal("missing client nonce on one of the exchanges")
	}
	if conns[0].clientNonce == conns[1].clientNonce {
		t.Error("client reused the nonce across reconnection")
	}
	for _, mc := range conns {
		if !mc.sentEmptyResponse || mc.sentAbort || !mc.capEndAfterSuccess {
			t.Errorf("incomplete SCRAM exchange on a reconnected connection: %+v", mc)
		}
	}
}

func TestSCRAMLargeMessagesChunking(t *testing.T) {
	server := newSCRAMMockServer(t, scramMockConfig{mech: scramMech, largeMessages: true})
	client := scramTestClient(server, scramMech, scramTestLogin, scramTestPassword)

	if err := client.Connect(); err != nil {
		t.Fatalf("Connect failed: %v", err)
	}
	defer func() {
		client.Quit()
		client.Wait()
	}()

	mc := server.firstConn()
	waitForRegistration(t, mc)
	if mc.sentAbort {
		t.Error("exchange aborted despite valid chunked messages")
	}
	if !mc.sentEmptyResponse || !mc.capEndAfterSuccess {
		t.Errorf("exchange did not complete correctly: %+v", mc)
	}
	if mc.largestChunkCount < 2 {
		t.Error("expected the server-first message to be split into multiple chunks")
	}
	if !mc.sentTerminator {
		t.Error("expected a terminating '+' after the exact 400-byte final chunk")
	}
	if mc.chunkTooLong {
		t.Error("an AUTHENTICATE chunk exceeded the 400-byte limit")
	}
}

func TestSCRAMServerSignatureFailure(t *testing.T) {
	server := newSCRAMMockServer(t, scramMockConfig{mech: scramMech, badSignature: true})
	client := scramTestClient(server, scramMech, scramTestLogin, scramTestPassword)

	err := client.Connect()
	if err == nil {
		client.Quit()
		client.Wait()
		t.Fatal("Connect succeeded despite a bad server signature")
	}
	if strings.Contains(err.Error(), scramTestPassword) {
		t.Errorf("returned error must not contain the password: %v", err)
	}

	mc := server.firstConn()
	if mc == nil {
		t.Fatal("no connection reached the mock server")
	}
	waitForAbort(t, mc)
	if mc.sentEmptyResponse {
		t.Error("client sent the completion AUTHENTICATE + despite signature failure")
	}
	if mc.capEndAfterSuccess {
		t.Error("CAP END must not be sent after a mandatory SASL failure")
	}
	assertEqual(client.State(), ConnectionNotStarted)
}

func TestSCRAMOptionalFallbackOnFailure(t *testing.T) {
	server := newSCRAMMockServer(t, scramMockConfig{
		mech:         scramMech,
		badSignature: true,
		send904:      true,
	})
	client := scramTestClient(server, scramMech, scramTestLogin, scramTestPassword)
	client.SASLOptional = true

	if err := client.Connect(); err != nil {
		t.Fatalf("Connect failed despite SASLOptional: %v", err)
	}
	defer func() {
		client.Quit()
		client.Wait()
	}()

	mc := server.firstConn()
	waitForAbort(t, mc)
	waitForRegistration(t, mc)
	if !mc.capEndReceived {
		t.Error("CAP END was not sent to continue registration after optional SASL failure")
	}
	if !mc.registrationDone {
		t.Error("registration did not continue after optional SASL failure")
	}
	if mc.capEndAfterSuccess {
		t.Error("CAP END must not be treated as a successful-SASL completion here")
	}
}

func TestSCRAMServerAbort(t *testing.T) {
	server := newSCRAMMockServer(t, scramMockConfig{mech: scramMech, serverAbort: true})
	client := scramTestClient(server, scramMech, scramTestLogin, scramTestPassword)

	err := client.Connect()
	if err == nil {
		client.Quit()
		client.Wait()
		t.Fatal("Connect succeeded despite the server aborting SASL")
	}
	if strings.Contains(err.Error(), scramTestPassword) {
		t.Errorf("returned error must not contain the password: %v", err)
	}
	mc := server.firstConn()
	if mc == nil {
		t.Fatal("no connection reached the mock server")
	}
	if mc.sentEmptyResponse {
		t.Error("client completed an exchange the server had aborted")
	}
	if mc.sentAbort {
		t.Error("client must not echo AUTHENTICATE * back when the server aborts")
	}
}

func TestSCRAMServerFirstValidationFailures(t *testing.T) {
	salt := base64.StdEncoding.EncodeToString([]byte("unit-test-salt-0123456789"))
	cases := []struct {
		name      string
		malformed func(clientNonce string) string
	}{
		{
			name: "nonce mismatch",
			malformed: func(clientNonce string) string {
				return fmt.Sprintf("r=%s,s=%s,i=4096", "totally-different-nonce", salt)
			},
		},
		{
			name: "nonce not extended",
			malformed: func(clientNonce string) string {
				return fmt.Sprintf("r=%s,s=%s,i=4096", clientNonce, salt)
			},
		},
		{
			name: "duplicate attribute",
			malformed: func(clientNonce string) string {
				return fmt.Sprintf("r=%s%s,s=%s,s=%s,i=4096", clientNonce, "srv", salt, salt)
			},
		},
		{
			name: "invalid salt",
			malformed: func(clientNonce string) string {
				return fmt.Sprintf("r=%s%s,s=!!!not-base64!!!,i=4096", clientNonce, "srv")
			},
		},
		{
			name: "zero iterations",
			malformed: func(clientNonce string) string {
				return fmt.Sprintf("r=%s%s,s=%s,i=0", clientNonce, "srv", salt)
			},
		},
		{
			name: "non-numeric iterations",
			malformed: func(clientNonce string) string {
				return fmt.Sprintf("r=%s%s,s=%s,i=abc", clientNonce, "srv", salt)
			},
		},
		{
			name: "missing iterations",
			malformed: func(clientNonce string) string {
				return fmt.Sprintf("r=%s%s,s=%s", clientNonce, "srv", salt)
			},
		},
		{
			name: "mandatory extension attribute",
			malformed: func(clientNonce string) string {
				return fmt.Sprintf("m=1,r=%s%s,s=%s,i=4096", clientNonce, "srv", salt)
			},
		},
		{
			name: "malformed attribute",
			malformed: func(clientNonce string) string {
				return fmt.Sprintf("r=%s%s,garbage,s=%s,i=4096", clientNonce, "srv", salt)
			},
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			server := newSCRAMMockServer(t, scramMockConfig{
				mech:                 scramMech,
				malformedServerFirst: tc.malformed,
			})
			client := scramTestClient(server, scramMech, scramTestLogin, scramTestPassword)

			err := client.Connect()
			if err == nil {
				client.Quit()
				client.Wait()
				t.Fatal("Connect succeeded despite an invalid server-first message")
			}
			if strings.Contains(err.Error(), scramTestPassword) {
				t.Errorf("error must not contain the password: %v", err)
			}
			mc := server.firstConn()
			if mc == nil {
				t.Fatal("no connection reached the mock server")
			}
			waitForAbort(t, mc)
			if mc.sentEmptyResponse {
				t.Error("client completed an exchange with an invalid server-first message")
			}
			assertEqual(client.State(), ConnectionNotStarted)
		})
	}
}

func TestPLAINStillWorks(t *testing.T) {
	server := newSCRAMMockServer(t, scramMockConfig{mech: "PLAIN"})
	client := scramTestClient(server, "PLAIN", scramTestLogin, scramTestPassword)

	if err := client.Connect(); err != nil {
		t.Fatalf("Connect failed: %v", err)
	}
	defer func() {
		client.Quit()
		client.Wait()
	}()

	mc := server.firstConn()
	waitForRegistration(t, mc)
	if !mc.capEndAfterSuccess {
		t.Error("PLAIN registration did not complete in the expected order")
	}
	if mc.sentAbort {
		t.Error("PLAIN exchange was aborted")
	}
}

func TestEXTERNALStillWorks(t *testing.T) {
	server := newSCRAMMockServer(t, scramMockConfig{mech: "EXTERNAL"})
	client := scramTestClient(server, "EXTERNAL", "", "")
	// EXTERNAL needs UseSASL without login/password
	client.UseSASL = true

	if err := client.Connect(); err != nil {
		t.Fatalf("Connect failed: %v", err)
	}
	defer func() {
		client.Quit()
		client.Wait()
	}()

	mc := server.firstConn()
	waitForRegistration(t, mc)
	if !mc.capEndAfterSuccess {
		t.Error("EXTERNAL registration did not complete in the expected order")
	}
	if mc.sentAbort {
		t.Error("EXTERNAL exchange was aborted")
	}
}

// --- pure unit tests ---

func TestSCRAMEscapeUsername(t *testing.T) {
	assertEqual(escapeSCRAMUsername("plain"), "plain")
	assertEqual(escapeSCRAMUsername("a=b"), "a=3Db")
	assertEqual(escapeSCRAMUsername("a,b"), "a=2Cb")
	assertEqual(escapeSCRAMUsername("=,,"), "=3D=2C=2C")
	assertEqual(escapeSCRAMUsername("=3D"), "=3D3D")
}

func TestSCRAMNonceGeneration(t *testing.T) {
	first, err := generateSCRAMNonce()
	if err != nil {
		t.Fatal(err)
	}
	second, err := generateSCRAMNonce()
	if err != nil {
		t.Fatal(err)
	}
	if first == second {
		t.Error("generated nonces are not unique")
	}
	for _, n := range []string{first, second} {
		if n == "" || strings.ContainsAny(n, ",=") {
			t.Errorf("nonce %q contains forbidden characters or is empty", n)
		}
	}
}

func TestPBKDF2KnownAnswer(t *testing.T) {
	// RFC 7914 section 11 test vector for PBKDF2-HMAC-SHA-256:
	// P="passwd", S="salt", c=1, dkLen=64
	derived := pbkdf2SHA256([]byte("passwd"), []byte("salt"), 1, 64)
	expected, err := hex.DecodeString("55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57c20dacbc49ca9cccf179b645991664b39d77ef317c71b845b1e30bd509112041d3a19783")
	if err != nil {
		t.Fatal(err)
	}
	assertEqual(bytes.Equal(derived, expected), true)
}

func TestSCRAMSessionRoundTrip(t *testing.T) {
	session, err := newSCRAMSession("user", "pencil")
	if err != nil {
		t.Fatal(err)
	}
	clientFirst := session.clientFirstMessage()
	if !bytes.HasPrefix(clientFirst, []byte("n,,")) {
		t.Fatalf("bad GS2 header: %q", clientFirst)
	}

	salt := []byte("pepper")
	iterations := 4096
	saltedPassword := testPBKDF2SHA256([]byte("pencil"), salt, iterations, sha256.Size)
	storedKey := testSHA256(testHMAC(saltedPassword, "Client Key"))
	serverKey := testHMAC(saltedPassword, "Server Key")

	fullNonce := session.clientNonce + "servernonce"
	serverFirst := fmt.Sprintf("r=%s,s=%s,i=%d",
		fullNonce, base64.StdEncoding.EncodeToString(salt), iterations)

	clientFinal, err := session.handleServerFirst([]byte(serverFirst))
	if err != nil {
		t.Fatalf("handleServerFirst failed: %v", err)
	}

	proofIndex := bytes.LastIndex(clientFinal, []byte(",p="))
	if proofIndex == -1 {
		t.Fatal("client-final missing proof")
	}
	noProof := string(clientFinal[:proofIndex])
	proof, err := base64.StdEncoding.DecodeString(string(clientFinal[proofIndex+3:]))
	if err != nil {
		t.Fatal(err)
	}
	authMessage := session.clientFirstBare + "," + serverFirst + "," + noProof
	signature := testHMAC(storedKey, authMessage)
	if !bytes.Equal(testSHA256(xorBytes(proof, signature)), storedKey) {
		t.Error("client proof does not check out")
	}

	serverFinal := "v=" + base64.StdEncoding.EncodeToString(testHMAC(serverKey, authMessage))
	if err := session.handleServerFinal([]byte(serverFinal)); err != nil {
		t.Fatalf("handleServerFinal failed: %v", err)
	}
	assertEqual(session.phase, scramVerified)

	// a tampered signature must fail on a fresh session with its own
	// freshly generated nonce
	session2, _ := newSCRAMSession("user", "pencil")
	serverFirst2 := fmt.Sprintf("r=%s%s,s=%s,i=%d",
		session2.clientNonce, "servernonce",
		base64.StdEncoding.EncodeToString(salt), iterations)
	clientFinal2, err := session2.handleServerFirst([]byte(serverFirst2))
	if err != nil {
		t.Fatal(err)
	}
	proofIndex2 := bytes.LastIndex(clientFinal2, []byte(",p="))
	noProof2 := string(clientFinal2[:proofIndex2])
	authMessage2 := session2.clientFirstBare + "," + serverFirst2 + "," + noProof2
	tampered := "v=" + base64.StdEncoding.EncodeToString(testSHA256(testHMAC(serverKey, authMessage2)))
	if err := session2.handleServerFinal([]byte(tampered)); err == nil {
		t.Error("tampered server signature was accepted")
	}

	// wrong-phase guards
	session3, _ := newSCRAMSession("user", "pencil")
	if err := session3.handleServerFinal([]byte(serverFinal)); err == nil {
		t.Error("server-final accepted before server-first")
	}
}

func TestSCRAMParseAttributes(t *testing.T) {
	attrs, err := parseSCRAMAttributes("r=abc,s=ZWo=,i=4096")
	if err != nil {
		t.Fatal(err)
	}
	assertEqual(len(attrs), 3)
	value, ok := scramAttributeValue(attrs, 'i')
	assertEqual(ok, true)
	assertEqual(value, "4096")

	if _, err := parseSCRAMAttributes("r=abc,r=def"); err == nil {
		t.Error("duplicate attributes must be rejected")
	}
	if _, err := parseSCRAMAttributes("r=abc,garbage"); err == nil {
		t.Error("malformed attributes must be rejected")
	}
	if _, err := parseSCRAMAttributes("m=1,r=abc"); err == nil {
		t.Error("the reserved m attribute must be rejected")
	}
}

func TestSCRAMUnsupportedMechStillRejected(t *testing.T) {
	client := &Connection{
		Server:       "127.0.0.1:0",
		Nick:         "x",
		SASLMech:     "BOGUS-MECH",
		UseSASL:      true,
		SASLLogin:    "u",
		SASLPassword: "p",
	}
	err := client.Connect()
	if err == nil {
		t.Error("expected unsupported mechanism error")
	}
	assertEqual(client.State(), ConnectionStopped)
	client.Wait()
}
