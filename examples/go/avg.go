// Example source (Go): the integer average — the midpoint-overflow bug again,
// now in Go.
//
//	avg(a, b) = (a + b) / 2
//
// Go unsigned arithmetic WRAPS on overflow (no panic, unlike Rust debug), so for
// large a, b the result is a wrapped (wrong) value — exactly like the C++ case.
// The checked Lean model reports OVERFLOW where a + b >= 2^32; the differential
// test surfaces that boundary.
//
// The leanlift Go oracle stages this file with a generated `main` in a temp
// module and `go build`s them together (SPEC §6).
package main

func avg(a uint32, b uint32) uint32 {
	return (a + b) / 2 // a + b WRAPS mod 2^32 on overflow
}
