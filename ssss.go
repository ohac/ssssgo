/*
 *  ssss version 0.5  -  Copyright 2005,2006 B. Poettering
 *
 *  This program is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License as
 *  published by the Free Software Foundation; either version 2 of the
 *  License, or (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
 *  02111-1307 USA
 */

/*
 * http://point-at-infinity.org/ssss/
 *
 * This is an implementation of Shamir's Secret Sharing Scheme. See
 *
 * You will need a system that has a /dev/random entropy source.
 */

package main

import (
	"bufio"
	"flag"
	"fmt"
	//big "github.com/ncw/gmp"
	"log"
	"math/big"
	"math/rand"
	"os"
)

var VERSION string = "0.5"
var RANDOM_SOURCE string = "/dev/random"
var MAXDEGREE int = 1024
var MAXTOKENLEN int = 128
var MAXLINELEN int = (MAXTOKENLEN + 1 + 10 + 1 + MAXDEGREE/4 + 10)

// coefficients of some irreducible polynomials over GF(2)
var irred_coeff = []byte{
	4, 3, 1, 5, 3, 1, 4, 3, 1, 7, 3, 2, 5, 4, 3, 5, 3, 2, 7, 4, 2, 4, 3, 1, 10, 9, 3, 9, 4, 2, 7, 6, 2, 10, 9,
	6, 4, 3, 1, 5, 4, 3, 4, 3, 1, 7, 2, 1, 5, 3, 2, 7, 4, 2, 6, 3, 2, 5, 3, 2, 15, 3, 2, 11, 3, 2, 9, 8, 7, 7,
	2, 1, 5, 3, 2, 9, 3, 1, 7, 3, 1, 9, 8, 3, 9, 4, 2, 8, 5, 3, 15, 14, 10, 10, 5, 2, 9, 6, 2, 9, 3, 2, 9, 5,
	2, 11, 10, 1, 7, 3, 2, 11, 2, 1, 9, 7, 4, 4, 3, 1, 8, 3, 1, 7, 4, 1, 7, 2, 1, 13, 11, 6, 5, 3, 2, 7, 3, 2,
	8, 7, 5, 12, 3, 2, 13, 10, 6, 5, 3, 2, 5, 3, 2, 9, 5, 2, 9, 7, 2, 13, 4, 3, 4, 3, 1, 11, 6, 4, 18, 9, 6,
	19, 18, 13, 11, 3, 2, 15, 9, 6, 4, 3, 1, 16, 5, 2, 15, 14, 6, 8, 5, 2, 15, 11, 2, 11, 6, 2, 7, 5, 3, 8,
	3, 1, 19, 16, 9, 11, 9, 6, 15, 7, 6, 13, 4, 3, 14, 13, 3, 13, 6, 3, 9, 5, 2, 19, 13, 6, 19, 10, 3, 11,
	6, 5, 9, 2, 1, 14, 3, 2, 13, 3, 1, 7, 5, 4, 11, 9, 8, 11, 6, 5, 23, 16, 9, 19, 14, 6, 23, 10, 2, 8, 3,
	2, 5, 4, 3, 9, 6, 4, 4, 3, 2, 13, 8, 6, 13, 11, 1, 13, 10, 3, 11, 6, 5, 19, 17, 4, 15, 14, 7, 13, 9, 6,
	9, 7, 3, 9, 7, 1, 14, 3, 2, 11, 8, 2, 11, 6, 4, 13, 5, 2, 11, 5, 1, 11, 4, 1, 19, 10, 3, 21, 10, 6, 13,
	3, 1, 15, 7, 5, 19, 18, 10, 7, 5, 3, 12, 7, 2, 7, 5, 1, 14, 9, 6, 10, 3, 2, 15, 13, 12, 12, 11, 9, 16,
	9, 7, 12, 9, 3, 9, 5, 2, 17, 10, 6, 24, 9, 3, 17, 15, 13, 5, 4, 3, 19, 17, 8, 15, 6, 3, 19, 6, 1}

var opt_quiet bool
var opt_QUIET bool
var opt_hex bool
var opt_diffusion bool = true

var opt_token string

var degree uint

var poly big.Int

// define mpz_lshift(A, B, l) mpz_mul_2exp(A, B, l)
// define mpz_sizeinbits(A) (mpz_cmp_ui(A, 0) ? mpz_sizeinbase(A, 2) : 0)

// emergency abort and warning functions

func warning(msg string) {
	if opt_QUIET {
		return
	}
	fmt.Printf("WARNING: %s.\n", msg)
}

/* field arithmetic routines */

func field_size_valid(deg int) bool {
	return deg >= 8 && deg <= MAXDEGREE && (deg%8) == 0
}

// initialize 'poly' to a bitfield representing the coefficients of an
// irreducible polynomial of degree 'deg'

func field_init(deg int) {
	if !field_size_valid(deg) {
		log.Fatal("field_init")
	}
	poly.SetBit(&poly, deg, 1)
	poly.SetBit(&poly, int(irred_coeff[3*(deg/8-1)+0]), 1)
	poly.SetBit(&poly, int(irred_coeff[3*(deg/8-1)+1]), 1)
	poly.SetBit(&poly, int(irred_coeff[3*(deg/8-1)+2]), 1)
	poly.SetBit(&poly, 0, 1)
	degree = uint(deg)
}

// I/O routines for GF(2^deg) field elements

func field_import(x *big.Int, s string, hexmode bool) {
	if hexmode {
		if len(s) > int(degree)/4 {
			log.Fatal("input string too long")
		}
		if len(s) < int(degree)/4 {
			warning("input string too short, adding null padding on the left")
		}
		_, ok := x.SetString(s, 16)
		if !ok {
			log.Fatal("invalid syntax")
		}
	} else {
		var warn bool
		if len(s) > int(degree)/8 {
			log.Fatal("input string too long")
		}
		for i := len(s) - 1; i >= 0; i-- {
			warn = warn || s[i] < 32 || s[i] >= 127
		}
		if warn {
			warning("binary data detected, use -x mode instead")
		}
		x.SetBytes([]byte(s))
	}
}

func field_print(x big.Int, hexmode bool) {
	if hexmode {
		for _, b := range x.Bytes() {
			fmt.Printf("%02x", b)
		}
		fmt.Println()
	} else {
		var printable, warn bool
		buf := x.Bytes()
		for _, b := range buf {
			printable = (b >= 32) && (b < 127)
			warn = warn || !printable
			if printable {
				fmt.Printf("%c", b)
			} else if hexmode {
				fmt.Printf("%02x", b) // TODO
			} else {
				fmt.Printf(".")
			}
		}
		fmt.Println()
		if warn {
			warning("binary data detected, use -x mode instead")
		}
	}
}

// basic field arithmetic in GF(2^deg)

func field_add(z, x, y *big.Int) {
	z.Xor(x, y)
}

func field_mult(z, x, y *big.Int) {
	var b big.Int
	var i uint
	// assert(z != y)
	b.Set(x)
	if y.Bit(0) != 0 {
		z.Set(&b)
	} else {
		z.SetUint64(0)
	}
	for i = 1; i < degree; i++ {
		b.Lsh(&b, 1)
		if b.Bit(int(degree)) != 0 {
			b.Xor(&b, &poly)
		}
		if y.Bit(int(i)) != 0 {
			z.Xor(z, &b)
		}
	}
}

func field_invert(z, x *big.Int) {
	var u, v, g, h, one big.Int
	//assert(mpz_cmp_ui(x, 0))
	u = *x
	v = poly
	g.SetUint64(0)
	z.SetUint64(1)
	_ = v
	one.SetUint64(1)
	for u.Cmp(&one) != 0 {
		// TODO
		i := 0 // TODO
		h.Lsh(&v, uint(i))
		u.Xor(&u, &h)
		h.Lsh(&g, uint(i))
		z.Xor(z, &h)
	}
	/*
					for mpz_cmp_ui(u, 1) {
	          i := mpz_sizeinbits(u) - mpz_sizeinbits(v)
						if i < 0 {
							//mpz_swap(u, v)
							//mpz_swap(z, g)
							i = -i
						}
						//mpz_lshift(h, v, i)
			      u.Xor(&u, &h)
						//mpz_lshift(h, g, i)
			      z.Xor(&z, &h)
					}
	*/
}

func cprng_read(x *big.Int) {
	buf := make([]byte, degree/8)
	for i := range buf {
		buf[i] = byte(rand.Uint32()) // TODO secure
	}
	x.SetBytes(buf)
}

// a 64 bit pseudo random permutation (based on the XTEA cipher)

func encipher_block(v []uint32) {
	var sum uint32
	var delta uint32 = 0x9E3779B9
	for i := 0; i < 32; i++ {
		v[0] += (((v[1] << 4) ^ (v[1] >> 5)) + v[1]) ^ sum
		sum += delta
		v[1] += (((v[0] << 4) ^ (v[0] >> 5)) + v[0]) ^ sum
	}
}

func decipher_block(v []uint32) {
	var sum uint32 = 0xC6EF3720
	var delta uint32 = 0x9E3779B9
	for i := 0; i < 32; i++ {
		v[1] -= ((v[0]<<4 ^ v[0]>>5) + v[0]) ^ sum
		sum -= delta
		v[0] -= ((v[1]<<4 ^ v[1]>>5) + v[1]) ^ sum
	}
}

func encode_slice(data []byte, idx, leng int, process_block func([]uint32)) {
	v := make([]uint32, 2)
	for i := 0; i < 2; i++ {
		/*
			v[i] = data[(idx+4*i)%leng]<<24 |
				data[(idx+4*i+1)%leng]<<16 |
				data[(idx+4*i+2)%leng]<<8 | data[(idx+4*i+3)%leng]
		*/
	}
	process_block(v)
	for i := 0; i < 2; i++ {
		data[(idx+4*i+0)%leng] = byte(v[i] >> 24)
		data[(idx+4*i+1)%leng] = byte((v[i] >> 16) & 0xff)
		data[(idx+4*i+2)%leng] = byte((v[i] >> 8) & 0xff)
		data[(idx+4*i+3)%leng] = byte(v[i] & 0xff)
	}
}

type encdec int

const (
	ENCODE encdec = iota
	DECODE
)

func encode_mpz(x *big.Int, encdecmode encdec) {
	v := make([]uint8, (MAXDEGREE+8)/16*2)
	//var t uint32
	//var i int
	//memset(v, 0, (degree+8)/16*2)
	//mpz_export(v, &t, -1, 2, 1, 0, x)
	if degree%16 == 8 {
		v[degree/8-1] = v[degree/8]
	}

	// 40 rounds are more than enough!
	if encdecmode == ENCODE {
		for i := 0; i < 40*(int(degree)/8); i += 2 {
			encode_slice(v, i, int(degree)/8, encipher_block)
		}
	} else {
		for i := 40*(int(degree)/8) - 2; i >= 0; i -= 2 {
			encode_slice(v, i, int(degree)/8, decipher_block)
		}
	}
	if degree%16 == 8 {
		v[degree/8] = v[degree/8-1]
		v[degree/8-1] = 0
	}
	//mpz_import(x, (degree+8)/16, -1, 2, 1, 0, v)
	//assert(mpz_sizeinbits(x) <= degree)
}

// evaluate polynomials efficiently

func horner(n int, y, x *big.Int, coeff []*big.Int) {
	y.Set(x) //mpz_set(y, x)
	for i := n - 1; i != 0; i-- {
		field_add(y, y, coeff[i])
		field_mult(y, y, x)
	}
	field_add(y, y, coeff[0])
}

// calculate the secret from a set of shares solving a linear equation system

/*
#define MPZ_SWAP(A, B) \
  do { mpz_set(h, A); mpz_set(A, B); mpz_set(B, h); } while(0)
*/

func restore_secret(n int /*, big.Int (*A)[n]*/, b []big.Int) int {
	//big.Int (*AA)[n] = (big.Int (*)[n])A
	//var found int
	var i, j, k int
	//var h big.Int
	for i = 0; i < n; i++ {
		//if !mpz_cmp_ui(AA[i][i], 0) {
		found := false
		for j = i + 1; j < n; j++ {
			/*
				if mpz_cmp_ui(AA[i][j], 0) {
					found = 1
					break
				}
			*/
		}
		if !found {
			return -1
		}
		for k = i; k < n; k++ {
			//MPZ_SWAP(AA[k][i], AA[k][j])
		}
		//MPZ_SWAP(b[i], b[j])
		//}
		for j = i + 1; j < n; j++ {
			/*
				if mpz_cmp_ui(AA[i][j], 0) {
					for k = i + 1; k < n; k++ {
						field_mult(h, AA[k][i], AA[i][j])
						field_mult(AA[k][j], AA[k][j], AA[i][i])
						field_add(AA[k][j], AA[k][j], h)
					}
					field_mult(h, b[i], AA[i][j])
					field_mult(b[j], b[j], AA[i][i])
					field_add(b[j], b[j], h)
				}
			*/
		}
	}
	//field_invert(&h, &AA[n-1][n-1])
	//field_mult(b[n-1], b[n-1], h)
	return 0
}

// Prompt for a secret, generate shares for it

func split(opt_threshold, opt_number, opt_security int) {
	var fmt_len uint = 1
	coeff := make([]*big.Int, opt_threshold)
	for i := range coeff {
		coeff[i] = new(big.Int)
	}
	for i := opt_number; i >= 10; i /= 10 {
		fmt_len++
	}

	if !opt_quiet {
		fmt.Printf("Generating shares using a (%d,%d) scheme with ",
			opt_threshold, opt_number)
		if opt_security > 0 {
			fmt.Print("a %d bit", opt_security)
		} else {
			fmt.Print("dynamic")
		}
		fmt.Println(" security level.")
		deg := opt_security
		if opt_security == 0 {
			deg = MAXDEGREE
		}
		fmt.Print("Enter the secret, ")
		if opt_hex {
			fmt.Printf("as most %d hex digits: ", deg/4)
		} else {
			fmt.Printf("at most %d ASCII characters: ", deg/8)
		}
	}

	// TODO echo off/on
	scanner := bufio.NewScanner(os.Stdin)
	if !scanner.Scan() {
		log.Fatal("no input")
	}
	buf := []byte(scanner.Text())

	if opt_security == 0 {
		if opt_hex {
			opt_security = 8 * ((len(buf) + 1) >> 1)
		} else {
			opt_security = 8 * len(buf)
		}
		if !field_size_valid(opt_security) {
			log.Fatal("security level invalid (secret too long?)")
		}
		if !opt_quiet {
			fmt.Printf("Using a %d bit security level.\n", opt_security)
		}
	}

	field_init(opt_security)

	field_import(coeff[0], string(buf), opt_hex)

	if opt_diffusion {
		if degree >= 64 {
			encode_mpz(coeff[0], ENCODE)
		} else {
			warning("security level too small for the diffusion layer")
		}
	}

	for i := 1; i < opt_threshold; i++ {
		cprng_read(coeff[i])
	}

	var x, y big.Int
	for i := 0; i < opt_number; i++ {
		x.SetUint64(uint64(i + 1)) // mpz_set_ui(x, i+1)
		horner(opt_threshold, &y, &x, coeff)
		if opt_token != "" {
			fmt.Printf("%s-", opt_token)
		}
		fmt.Printf("%0*d-", fmt_len, i+1)
		field_print(y, true)
	}
}

// Prompt for shares, calculate the secret

func combine(opt_threshold int) {
	//A := make([]big.Int, opt_threshold) // A[opt_threshold][opt_threshold]
	y := make([]big.Int, opt_threshold)
	var x big.Int
	_ = x
	var b []byte
	var s uint

	if !opt_quiet {
		fmt.Printf("Enter %d shares separated by newlines:\n", opt_threshold)
	}
	for i := 0; i < opt_threshold; i++ {
		if !opt_quiet {
			fmt.Printf("Share [%d/%d]: ", i+1, opt_threshold)
		}
		scanner := bufio.NewScanner(os.Stdin)
		if !scanner.Scan() {
			log.Fatal("I/O error while reading shares")
		}
		buf := []byte(scanner.Text())
		_ = buf

		/*
						a = strchr(buf, '-')
						if !a {
			        log.Fatal("invalid syntax")
						}
		*/
		//*a++ = 0
		/*
			b = strchr(a, '-')
			if b {
				//*b++ = 0
			} else {
				b = a
				a = buf
			}
		*/

		if s == 0 {
			s = uint(4 * len(b))
			if !field_size_valid(int(s)) {
				log.Fatal("share has illegal length")
			}
			field_init(int(s))
		} else {
			if s != uint(4*len(b)) {
				log.Fatal("shares have different security levels")
			}
		}

		//j := atoi(a)
		/*
			if j == 0 {
			log.Fatal("invalid share")
			}
		*/
		//mpz_set_ui(x, j)
		//mpz_init_set_ui(A[opt_threshold-1][i], 1)
		for j := opt_threshold - 2; j >= 0; j-- {
			//field_mult(A[j][i], A[j+1][i], x)
		}
		//field_import(&y[i], string(b), 1)
		//field_mult(x, x, A[0][i])
		//field_add(y[i], y[i], x)
	}
	/*
		if restore_secret(opt_threshold, A, y) != 0 {
			log.Fatal("shares inconsistent. Perhaps a single share was used twice")
		}
	*/

	if opt_diffusion {
		if degree >= 64 {
			//encode_mpz(&y[opt_threshold-1], DECODE)
		} else {
			warning("security level too small for the diffusion layer")
		}
	}

	if !opt_quiet {
		fmt.Print("Resulting secret: ")
	}
	field_print(y[opt_threshold-1], opt_hex)
}

func main() {
	// TODO mlockall
	// TODO seteuid
	// TODO echo off

	opt_showversion := flag.Bool("v", false, "show version")
	opt_diffusion := flag.Bool("D", false, "opt_diffusion")
	opt_help := flag.Bool("h", false, "help")
	opt_quiet := flag.Bool("q", false, "quiet")
	opt_QUIET := flag.Bool("Q", false, "QUIET")
	opt_hex := flag.Bool("x", false, "hex")

	opt_security := flag.Int("s", 0, "security")
	opt_threshold := flag.Int("t", 2, "threshold")
	opt_number := flag.Int("n", 3, "number")
	opt_token := flag.String("w", "", "token")

	_ = opt_diffusion
	_ = opt_hex

	flag.Parse()

	if *opt_QUIET {
		opt_quiet = opt_QUIET
	}
	_ = opt_quiet

	args := flag.Args()
	if len(args) == 0 {
		fmt.Println("ssss [options] [split/combine]\n" +
			"help: ssss --help\n" +
			"help: ssss -h split\n" +
			"help: ssss -h combine")
		os.Exit(0)
	}
	name := args[0]

	if name == "split" {
		if *opt_help || *opt_showversion {
			fmt.Println("Split secrets using Shamir's Secret Sharing Scheme.\n" +
				"\n" +
				"ssss [-t threshold] [-n shares] [-w token] [-s level]" +
				" [-x] [-q] [-Q] [-D] [-v] split")
			if *opt_showversion {
				fmt.Println("\nVersion: " + VERSION)
			}
			os.Exit(0)
		}

		if *opt_threshold < 2 {
			log.Fatal("invalid parameters: invalid threshold value")
		}
		if *opt_number < *opt_threshold {
			log.Fatal("invalid parameters: number of shares smaller than threshold")
		}

		if *opt_security != 0 && !field_size_valid(*opt_security) {
			log.Fatal("invalid parameters: invalid security level")
		}

		if *opt_token != "" && len(*opt_token) > MAXTOKENLEN {
			log.Fatal("invalid parameters: token too long")
		}
		split(*opt_threshold, *opt_number, *opt_security)
	} else {
		if *opt_help || *opt_showversion {
			fmt.Println("Combine shares using Shamir's Secret Sharing Scheme.\n" +
				"\n" +
				"ssss -t threshold [-x] [-q] [-Q] [-D] [-v]")
			if *opt_showversion {
				fmt.Println("\nVersion: " + VERSION)
			}
			os.Exit(0)
		}
		if *opt_threshold < 2 {
			log.Fatal("invalid parameters: invalid threshold value")
		}
		combine(*opt_threshold)
	}
}
