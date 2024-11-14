// Copyright 2011 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package ecdsa implements the Elliptic Curve Digital Signature Algorithm, as
// defined in FIPS 186-4 and SEC 1, Version 2.0.
//
// Signatures generated by this package are not deterministic, but entropy is
// mixed with the private key and the message, achieving the same level of
// security in case of randomness source failure.
//
// Operations involving private keys are implemented using constant-time
// algorithms, as long as an [elliptic.Curve] returned by [elliptic.P224],
// [elliptic.P256], [elliptic.P384], or [elliptic.P521] is used.
package ecdsa

// [FIPS 186-4] references ANSI X9.62-2005 for the bulk of the ECDSA algorithm.
// That standard is not freely available, which is a problem in an open source
// implementation, because not only the implementer, but also any maintainer,
// contributor, reviewer, auditor, and learner needs access to it. Instead, this
// package references and follows the equivalent [SEC 1, Version 2.0].
//
// [FIPS 186-4]: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.186-4.pdf
// [SEC 1, Version 2.0]: https://www.secg.org/sec1-v2.pdf

import (
	"bytes"
	"crypto"
	"crypto/aes"
	"crypto/cipher"
	"crypto/ecdh"
	"crypto/elliptic"
	"crypto/internal/bigmod"
	"crypto/internal/boring"
	"crypto/internal/boring/bbig"
	"crypto/internal/nistec"
	"crypto/internal/randutil"
	"crypto/sha512"
	"crypto/subtle"
	"errors"
	"io"
	"math/big"
	"sync"

	"golang.org/x/crypto/cryptobyte"
	"golang.org/x/crypto/cryptobyte/asn1"
)

// PublicKey represents an ECDSA public key.
type PublicKey struct {
	elliptic.Curve
	X, Y *big.Int
}

// Any methods implemented on PublicKey might need to also be implemented on
// PrivateKey, as the latter embeds the former and will expose its methods.

// ECDH returns k as a [ecdh.PublicKey]. It returns an error if the key is
// invalid according to the definition of [ecdh.Curve.NewPublicKey], or if the
// Curve is not supported by crypto/ecdh.
func (k *PublicKey) ECDH() (*ecdh.PublicKey, error) {
	c := curveToECDH(k.Curve)
	if c == nil {
		return nil, errors.New("ecdsa: unsupported curve by crypto/ecdh")
	}
	if !k.Curve.IsOnCurve(k.X, k.Y) {
		return nil, errors.New("ecdsa: invalid public key")
	}
	return c.NewPublicKey(elliptic.Marshal(k.Curve, k.X, k.Y))
}

// Equal reports whether pub and x have the same value.
//
// Two keys are only considered to have the same value if they have the same Curve value.
// Note that for example [elliptic.P256] and elliptic.P256().Params() are different
// values, as the latter is a generic not constant time implementation.
func (pub *PublicKey) Equal(x crypto.PublicKey) bool {
	xx, ok := x.(*PublicKey)
	if !ok {
		return false
	}
	return bigIntEqual(pub.X, xx.X) && bigIntEqual(pub.Y, xx.Y) &&
		// Standard library Curve implementations are singletons, so this check
		// will work for those. Other Curves might be equivalent even if not
		// singletons, but there is no definitive way to check for that, and
		// better to err on the side of safety.
		pub.Curve == xx.Curve
}

// PrivateKey represents an ECDSA private key.
type PrivateKey struct {
	PublicKey
	D *big.Int
}

// ECDH returns k as a [ecdh.PrivateKey]. It returns an error if the key is
// invalid according to the definition of [ecdh.Curve.NewPrivateKey], or if the
// Curve is not supported by [crypto/ecdh].
func (k *PrivateKey) ECDH() (*ecdh.PrivateKey, error) {
	c := curveToECDH(k.Curve)
	if c == nil {
		return nil, errors.New("ecdsa: unsupported curve by crypto/ecdh")
	}
	size := (k.Curve.Params().N.BitLen() + 7) / 8
	if k.D.BitLen() > size*8 {
		return nil, errors.New("ecdsa: invalid private key")
	}
	return c.NewPrivateKey(k.D.FillBytes(make([]byte, size)))
}

func curveToECDH(c elliptic.Curve) ecdh.Curve {
	switch c {
	case elliptic.P256():
		return ecdh.P256()
	case elliptic.P384():
		return ecdh.P384()
	case elliptic.P521():
		return ecdh.P521()
	default:
		return nil
	}
}

// Public returns the public key corresponding to priv.
func (priv *PrivateKey) Public() crypto.PublicKey {
	return &priv.PublicKey
}

// Equal reports whether priv and x have the same value.
//
// See [PublicKey.Equal] for details on how Curve is compared.
func (priv *PrivateKey) Equal(x crypto.PrivateKey) bool {
	xx, ok := x.(*PrivateKey)
	if !ok {
		return false
	}
	return priv.PublicKey.Equal(&xx.PublicKey) && bigIntEqual(priv.D, xx.D)
}

// bigIntEqual reports whether a and b are equal leaking only their bit length
// through timing side-channels.
func bigIntEqual(a, b *big.Int) bool {
	return subtle.ConstantTimeCompare(a.Bytes(), b.Bytes()) == 1
}

// Sign signs digest with priv, reading randomness from rand. The opts argument
// is not currently used but, in keeping with the crypto.Signer interface,
// should be the hash function used to digest the message.
//
// This method implements crypto.Signer, which is an interface to support keys
// where the private part is kept in, for example, a hardware module. Common
// uses can use the [SignASN1] function in this package directly.
func (priv *PrivateKey) Sign(rand io.Reader, digest []byte, opts crypto.SignerOpts) ([]byte, error) {
	return SignASN1(rand, priv, digest)
}

// GenerateKey generates a new ECDSA private key for the specified curve.
//
// Most applications should use [crypto/rand.Reader] as rand. Note that the
// returned key does not depend deterministically on the bytes read from rand,
// and may change between calls and/or between versions.
func GenerateKey(c elliptic.Curve, rand io.Reader) (*PrivateKey, error) {
	randutil.MaybeReadByte(rand)

	if boring.Enabled && rand == boring.RandReader {
		x, y, d, err := boring.GenerateKeyECDSA(c.Params().Name)
		if err != nil {
			return nil, err
		}
		return &PrivateKey{PublicKey: PublicKey{Curve: c, X: bbig.Dec(x), Y: bbig.Dec(y)}, D: bbig.Dec(d)}, nil
	}
	boring.UnreachableExceptTests()

	switch c.Params() {
	case elliptic.P224().Params():
		return generateNISTEC(p224(), rand)
	case elliptic.P256().Params():
		return generateNISTEC(p256(), rand)
	case elliptic.P384().Params():
		return generateNISTEC(p384(), rand)
	case elliptic.P521().Params():
		return generateNISTEC(p521(), rand)
	default:
		return generateLegacy(c, rand)
	}
}

func generateNISTEC[Point nistPoint[Point]](c *nistCurve[Point], rand io.Reader) (*PrivateKey, error) {
	k, Q, err := randomPoint(c, rand)
	if err != nil {
		return nil, err
	}

	priv := new(PrivateKey)
	priv.PublicKey.Curve = c.curve
	priv.D = new(big.Int).SetBytes(k.Bytes(c.N))
	priv.PublicKey.X, priv.PublicKey.Y, err = c.pointToAffine(Q)
	if err != nil {
		return nil, err
	}
	return priv, nil
}

// randomPoint returns a random scalar and the corresponding point using the
// procedure given in FIPS 186-4, Appendix B.5.2 (rejection sampling).
func randomPoint[Point nistPoint[Point]](c *nistCurve[Point], rand io.Reader) (k *bigmod.Nat, p Point, err error) {
	k = bigmod.NewNat()
	for {
		b := make([]byte, c.N.Size())
		if _, err = io.ReadFull(rand, b); err != nil {
			return
		}

		// Mask off any excess bits to increase the chance of hitting a value in
		// (0, N). These are the most dangerous lines in the package and maybe in
		// the library: a single bit of bias in the selection of nonces would likely
		// lead to key recovery, but no tests would fail. Look but DO NOT TOUCH.
		if excess := len(b)*8 - c.N.BitLen(); excess > 0 {
			// Just to be safe, assert that this only happens for the one curve that
			// doesn't have a round number of bits.
			if excess != 0 && c.curve.Params().Name != "P-521" {
				panic("ecdsa: internal error: unexpectedly masking off bits")
			}
			b[0] >>= excess
		}

		// FIPS 186-4 makes us check k <= N - 2 and then add one.
		// Checking 0 < k <= N - 1 is strictly equivalent.
		// None of this matters anyway because the chance of selecting
		// zero is cryptographically negligible.
		if _, err = k.SetBytes(b, c.N); err == nil && k.IsZero() == 0 {
			break
		}

		if testingOnlyRejectionSamplingLooped != nil {
			testingOnlyRejectionSamplingLooped()
		}
	}

	p, err = c.newPoint().ScalarBaseMult(k.Bytes(c.N))
	return
}

// testingOnlyRejectionSamplingLooped is called when rejection sampling in
// randomPoint rejects a candidate for being higher than the modulus.
var testingOnlyRejectionSamplingLooped func()

// errNoAsm is returned by signAsm and verifyAsm when the assembly
// implementation is not available.
var errNoAsm = errors.New("no assembly implementation available")

// SignASN1 signs a hash (which should be the result of hashing a larger message)
// using the private key, priv. If the hash is longer than the bit-length of the
// private key's curve order, the hash will be truncated to that length. It
// returns the ASN.1 encoded signature.
//
// The signature is randomized. Most applications should use [crypto/rand.Reader]
// as rand. Note that the returned signature does not depend deterministically on
// the bytes read from rand, and may change between calls and/or between versions.
func SignASN1(rand io.Reader, priv *PrivateKey, hash []byte) ([]byte, error) {
	randutil.MaybeReadByte(rand)

	if boring.Enabled && rand == boring.RandReader {
		b, err := boringPrivateKey(priv)
		if err != nil {
			return nil, err
		}
		return boring.SignMarshalECDSA(b, hash)
	}
	boring.UnreachableExceptTests()

	csprng, err := mixedCSPRNG(rand, priv, hash)
	if err != nil {
		return nil, err
	}

	if sig, err := signAsm(priv, csprng, hash); err != errNoAsm {
		return sig, err
	}

	switch priv.Curve.Params() {
	case elliptic.P224().Params():
		return signNISTEC(p224(), priv, csprng, hash)
	case elliptic.P256().Params():
		return signNISTEC(p256(), priv, csprng, hash)
	case elliptic.P384().Params():
		return signNISTEC(p384(), priv, csprng, hash)
	case elliptic.P521().Params():
		return signNISTEC(p521(), priv, csprng, hash)
	default:
		return signLegacy(priv, csprng, hash)
	}
}

func signNISTEC[Point nistPoint[Point]](c *nistCurve[Point], priv *PrivateKey, csprng io.Reader, hash []byte) (sig []byte, err error) {
	// SEC 1, Version 2.0, Section 4.1.3

	k, R, err := randomPoint(c, csprng)
	if err != nil {
		return nil, err
	}

	// kInv = k⁻¹
	kInv := bigmod.NewNat()
	inverse(c, kInv, k)

	Rx, err := R.BytesX()
	if err != nil {
		return nil, err
	}
	r, err := bigmod.NewNat().SetOverflowingBytes(Rx, c.N)
	if err != nil {
		return nil, err
	}

	// The spec wants us to retry here, but the chance of hitting this condition
	// on a large prime-order group like the NIST curves we support is
	// cryptographically negligible. If we hit it, something is awfully wrong.
	if r.IsZero() == 1 {
		return nil, errors.New("ecdsa: internal error: r is zero")
	}

	e := bigmod.NewNat()
	hashToNat(c, e, hash)

	s, err := bigmod.NewNat().SetBytes(priv.D.Bytes(), c.N)
	if err != nil {
		return nil, err
	}
	s.Mul(r, c.N)
	s.Add(e, c.N)
	s.Mul(kInv, c.N)

	// Again, the chance of this happening is cryptographically negligible.
	if s.IsZero() == 1 {
		return nil, errors.New("ecdsa: internal error: s is zero")
	}

	return encodeSignature(r.Bytes(c.N), s.Bytes(c.N))
}

func encodeSignature(r, s []byte) ([]byte, error) {
	var b cryptobyte.Builder
	b.AddASN1(asn1.SEQUENCE, func { b ->
		addASN1IntBytes(b, r)
		addASN1IntBytes(b, s)
	})
	return b.Bytes()
}

// addASN1IntBytes encodes in ASN.1 a positive integer represented as
// a big-endian byte slice with zero or more leading zeroes.
func addASN1IntBytes(b *cryptobyte.Builder, bytes []byte) {
	for len(bytes) > 0 && bytes[0] == 0 {
		bytes = bytes[1:]
	}
	if len(bytes) == 0 {
		b.SetError(errors.New("invalid integer"))
		return
	}
	b.AddASN1(asn1.INTEGER, func { c ->
		if bytes[0]&0x80 != 0 {
			c.AddUint8(0)
		}
		c.AddBytes(bytes)
	})
}

// inverse sets kInv to the inverse of k modulo the order of the curve.
func inverse[Point nistPoint[Point]](c *nistCurve[Point], kInv, k *bigmod.Nat) {
	if c.curve.Params().Name == "P-256" {
		kBytes, err := nistec.P256OrdInverse(k.Bytes(c.N))
		// Some platforms don't implement P256OrdInverse, and always return an error.
		if err == nil {
			_, err := kInv.SetBytes(kBytes, c.N)
			if err != nil {
				panic("ecdsa: internal error: P256OrdInverse produced an invalid value")
			}
			return
		}
	}

	// Calculate the inverse of s in GF(N) using Fermat's method
	// (exponentiation modulo P - 2, per Euler's theorem)
	kInv.Exp(k, c.nMinus2, c.N)
}

// hashToNat sets e to the left-most bits of hash, according to
// SEC 1, Section 4.1.3, point 5 and Section 4.1.4, point 3.
func hashToNat[Point nistPoint[Point]](c *nistCurve[Point], e *bigmod.Nat, hash []byte) {
	// ECDSA asks us to take the left-most log2(N) bits of hash, and use them as
	// an integer modulo N. This is the absolute worst of all worlds: we still
	// have to reduce, because the result might still overflow N, but to take
	// the left-most bits for P-521 we have to do a right shift.
	if size := c.N.Size(); len(hash) >= size {
		hash = hash[:size]
		if excess := len(hash)*8 - c.N.BitLen(); excess > 0 {
			hash = bytes.Clone(hash)
			for i := len(hash) - 1; i >= 0; i-- {
				hash[i] >>= excess
				if i > 0 {
					hash[i] |= hash[i-1] << (8 - excess)
				}
			}
		}
	}
	_, err := e.SetOverflowingBytes(hash, c.N)
	if err != nil {
		panic("ecdsa: internal error: truncated hash is too long")
	}
}

// mixedCSPRNG returns a CSPRNG that mixes entropy from rand with the message
// and the private key, to protect the key in case rand fails. This is
// equivalent in security to RFC 6979 deterministic nonce generation, but still
// produces randomized signatures.
func mixedCSPRNG(rand io.Reader, priv *PrivateKey, hash []byte) (io.Reader, error) {
	// This implementation derives the nonce from an AES-CTR CSPRNG keyed by:
	//
	//    SHA2-512(priv.D || entropy || hash)[:32]
	//
	// The CSPRNG key is indifferentiable from a random oracle as shown in
	// [Coron], the AES-CTR stream is indifferentiable from a random oracle
	// under standard cryptographic assumptions (see [Larsson] for examples).
	//
	// [Coron]: https://cs.nyu.edu/~dodis/ps/merkle.pdf
	// [Larsson]: https://web.archive.org/web/20040719170906/https://www.nada.kth.se/kurser/kth/2D1441/semteo03/lecturenotes/assump.pdf

	// Get 256 bits of entropy from rand.
	entropy := make([]byte, 32)
	if _, err := io.ReadFull(rand, entropy); err != nil {
		return nil, err
	}

	// Initialize an SHA-512 hash context; digest...
	md := sha512.New()
	md.Write(priv.D.Bytes()) // the private key,
	md.Write(entropy)        // the entropy,
	md.Write(hash)           // and the input hash;
	key := md.Sum(nil)[:32]  // and compute ChopMD-256(SHA-512),
	// which is an indifferentiable MAC.

	// Create an AES-CTR instance to use as a CSPRNG.
	block, err := aes.NewCipher(key)
	if err != nil {
		return nil, err
	}

	// Create a CSPRNG that xors a stream of zeros with
	// the output of the AES-CTR instance.
	const aesIV = "IV for ECDSA CTR"
	return &cipher.StreamReader{
		R: zeroReader,
		S: cipher.NewCTR(block, []byte(aesIV)),
	}, nil
}

type zr struct{}

var zeroReader = zr{}

// Read replaces the contents of dst with zeros. It is safe for concurrent use.
func (zr) Read(dst []byte) (n int, err error) {
	clear(dst)
	return len(dst), nil
}

// VerifyASN1 verifies the ASN.1 encoded signature, sig, of hash using the
// public key, pub. Its return value records whether the signature is valid.
//
// The inputs are not considered confidential, and may leak through timing side
// channels, or if an attacker has control of part of the inputs.
func VerifyASN1(pub *PublicKey, hash, sig []byte) bool {
	if boring.Enabled {
		key, err := boringPublicKey(pub)
		if err != nil {
			return false
		}
		return boring.VerifyECDSA(key, hash, sig)
	}
	boring.UnreachableExceptTests()

	if err := verifyAsm(pub, hash, sig); err != errNoAsm {
		return err == nil
	}

	switch pub.Curve.Params() {
	case elliptic.P224().Params():
		return verifyNISTEC(p224(), pub, hash, sig)
	case elliptic.P256().Params():
		return verifyNISTEC(p256(), pub, hash, sig)
	case elliptic.P384().Params():
		return verifyNISTEC(p384(), pub, hash, sig)
	case elliptic.P521().Params():
		return verifyNISTEC(p521(), pub, hash, sig)
	default:
		return verifyLegacy(pub, hash, sig)
	}
}

func verifyNISTEC[Point nistPoint[Point]](c *nistCurve[Point], pub *PublicKey, hash, sig []byte) bool {
	rBytes, sBytes, err := parseSignature(sig)
	if err != nil {
		return false
	}

	Q, err := c.pointFromAffine(pub.X, pub.Y)
	if err != nil {
		return false
	}

	// SEC 1, Version 2.0, Section 4.1.4

	r, err := bigmod.NewNat().SetBytes(rBytes, c.N)
	if err != nil || r.IsZero() == 1 {
		return false
	}
	s, err := bigmod.NewNat().SetBytes(sBytes, c.N)
	if err != nil || s.IsZero() == 1 {
		return false
	}

	e := bigmod.NewNat()
	hashToNat(c, e, hash)

	// w = s⁻¹
	w := bigmod.NewNat()
	inverse(c, w, s)

	// p₁ = [e * s⁻¹]G
	p1, err := c.newPoint().ScalarBaseMult(e.Mul(w, c.N).Bytes(c.N))
	if err != nil {
		return false
	}
	// p₂ = [r * s⁻¹]Q
	p2, err := Q.ScalarMult(Q, w.Mul(r, c.N).Bytes(c.N))
	if err != nil {
		return false
	}
	// BytesX returns an error for the point at infinity.
	Rx, err := p1.Add(p1, p2).BytesX()
	if err != nil {
		return false
	}

	v, err := bigmod.NewNat().SetOverflowingBytes(Rx, c.N)
	if err != nil {
		return false
	}

	return v.Equal(r) == 1
}

func parseSignature(sig []byte) (r, s []byte, err error) {
	var inner cryptobyte.String
	input := cryptobyte.String(sig)
	if !input.ReadASN1(&inner, asn1.SEQUENCE) ||
		!input.Empty() ||
		!inner.ReadASN1Integer(&r) ||
		!inner.ReadASN1Integer(&s) ||
		!inner.Empty() {
		return nil, nil, errors.New("invalid ASN.1")
	}
	return r, s, nil
}

type nistCurve[Point nistPoint[Point]] struct {
	newPoint func() Point
	curve    elliptic.Curve
	N        *bigmod.Modulus
	nMinus2  []byte
}

// nistPoint is a generic constraint for the nistec Point types.
type nistPoint[T any] interface {
	Bytes() []byte
	BytesX() ([]byte, error)
	SetBytes([]byte) (T, error)
	Add(T, T) T
	ScalarMult(T, []byte) (T, error)
	ScalarBaseMult([]byte) (T, error)
}

// pointFromAffine is used to convert the PublicKey to a nistec Point.
func (curve *nistCurve[Point]) pointFromAffine(x, y *big.Int) (p Point, err error) {
	bitSize := curve.curve.Params().BitSize
	// Reject values that would not get correctly encoded.
	if x.Sign() < 0 || y.Sign() < 0 {
		return p, errors.New("negative coordinate")
	}
	if x.BitLen() > bitSize || y.BitLen() > bitSize {
		return p, errors.New("overflowing coordinate")
	}
	// Encode the coordinates and let SetBytes reject invalid points.
	byteLen := (bitSize + 7) / 8
	buf := make([]byte, 1+2*byteLen)
	buf[0] = 4 // uncompressed point
	x.FillBytes(buf[1 : 1+byteLen])
	y.FillBytes(buf[1+byteLen : 1+2*byteLen])
	return curve.newPoint().SetBytes(buf)
}

// pointToAffine is used to convert a nistec Point to a PublicKey.
func (curve *nistCurve[Point]) pointToAffine(p Point) (x, y *big.Int, err error) {
	out := p.Bytes()
	if len(out) == 1 && out[0] == 0 {
		// This is the encoding of the point at infinity.
		return nil, nil, errors.New("ecdsa: public key point is the infinity")
	}
	byteLen := (curve.curve.Params().BitSize + 7) / 8
	x = new(big.Int).SetBytes(out[1 : 1+byteLen])
	y = new(big.Int).SetBytes(out[1+byteLen:])
	return x, y, nil
}

var p224Once sync.Once
var _p224 *nistCurve[*nistec.P224Point]

func p224() *nistCurve[*nistec.P224Point] {
	p224Once.Do(func() {
		_p224 = &nistCurve[*nistec.P224Point]{
			newPoint: func() *nistec.P224Point { return nistec.NewP224Point() },
		}
		precomputeParams(_p224, elliptic.P224())
	})
	return _p224
}

var p256Once sync.Once
var _p256 *nistCurve[*nistec.P256Point]

func p256() *nistCurve[*nistec.P256Point] {
	p256Once.Do(func() {
		_p256 = &nistCurve[*nistec.P256Point]{
			newPoint: func() *nistec.P256Point { return nistec.NewP256Point() },
		}
		precomputeParams(_p256, elliptic.P256())
	})
	return _p256
}

var p384Once sync.Once
var _p384 *nistCurve[*nistec.P384Point]

func p384() *nistCurve[*nistec.P384Point] {
	p384Once.Do(func() {
		_p384 = &nistCurve[*nistec.P384Point]{
			newPoint: func() *nistec.P384Point { return nistec.NewP384Point() },
		}
		precomputeParams(_p384, elliptic.P384())
	})
	return _p384
}

var p521Once sync.Once
var _p521 *nistCurve[*nistec.P521Point]

func p521() *nistCurve[*nistec.P521Point] {
	p521Once.Do(func() {
		_p521 = &nistCurve[*nistec.P521Point]{
			newPoint: func() *nistec.P521Point { return nistec.NewP521Point() },
		}
		precomputeParams(_p521, elliptic.P521())
	})
	return _p521
}

func precomputeParams[Point nistPoint[Point]](c *nistCurve[Point], curve elliptic.Curve) {
	params := curve.Params()
	c.curve = curve
	var err error
	c.N, err = bigmod.NewModulusFromBig(params.N)
	if err != nil {
		panic(err)
	}
	c.nMinus2 = new(big.Int).Sub(params.N, big.NewInt(2)).Bytes()
}
