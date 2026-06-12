// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Fresh Solidity example: the 2-term dot product `a*b + c*d`, computed in an
// `unchecked` block. Solidity 0.8+ arithmetic normally REVERTS on overflow (which
// would match the checked Lean model), but inside `unchecked` it WRAPS mod 2^32 —
// the realistic Solidity overflow bug. So like the C++/Go cases, the checked Lean
// model reports OVERFLOW where the source silently wraps, and the differential
// test against the EVM oracle surfaces that boundary.
//
// The leanlift Solidity oracle executes this on an EVM (SPEC §6): a forge script
// deploys the contract and calls `dot2` per vector, the result being return data.
contract Dot2 {
    function dot2(uint32 a, uint32 b, uint32 c, uint32 d) external pure returns (uint32) {
        unchecked {
            return a * b + c * d; // uint32: WRAPS mod 2^32 on overflow
        }
    }
}
