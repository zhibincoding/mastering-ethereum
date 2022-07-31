// Copyright 2014 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package vm

import (
	"errors"
	"fmt"
)

// List evm execution errors
var (
	ErrOutOfGas = errors.New("out of gas")
	// * 用来触发OOG Error
	ErrCodeStoreOutOfGas = errors.New("contract creation code storage out of gas")
	ErrDepth             = errors.New("max call depth exceeded")
	// * 与外层error.go中定义的ErrInsufficientFund不同
	ErrInsufficientBalance      = errors.New("insufficient balance for transfer")
	ErrContractAddressCollision = errors.New("contract address collision")
	ErrExecutionReverted        = errors.New("execution reverted")
	ErrMaxCodeSizeExceeded      = errors.New("max code size exceeded")
	ErrInvalidJump              = errors.New("invalid jump destination")
	ErrWriteProtection          = errors.New("write protection")
	ErrReturnDataOutOfBounds    = errors.New("return data out of bounds")
	ErrGasUintOverflow          = errors.New("gas uint64 overflow")
	ErrInvalidCode              = errors.New("invalid code: must not begin with 0xef")
	ErrNonceUintOverflow        = errors.New("nonce uint64 overflow")

	// errStopToken is an internal token indicating interpreter loop termination,
	// never returned to outside callers.
	errStopToken = errors.New("stop token")
)

// ErrStackUnderflow wraps an evm error when the items on the stack less
// than the minimal requirement.
// * todo: less
// * overflow和underflow处理起来是差不多的，只要解决了其中一个，另外一个并不难解决
type ErrStackUnderflow struct {
	stackLen int
	required int
}

func (e *ErrStackUnderflow) Error() string {
	return fmt.Sprintf("stack underflow (%d <=> %d)", e.stackLen, e.required)
}

// ErrStackOverflow wraps an evm error when the items on the stack exceeds
// the maximum allowance.
// * stack上的item超过最大允许值的时候，就会弹出这个stackOverflow的error
// * EVM的stack深度是1024（这个就是在params文件中定义的stackLimit）
type ErrStackOverflow struct {
	// * stackLen应该是目前stack上item的深度
	// * limit应该是params.stackLimit = 1024
	stackLen int
	limit    int
}

func (e *ErrStackOverflow) Error() string {
	// * 出现stack overflow就弹出这段报错提醒
	// * stack limit reached 1026 (1024)
	return fmt.Sprintf("stack limit reached %d (%d)", e.stackLen, e.limit)

	// ! stack limit reached 1024 (1023)
}

// ErrInvalidOpCode wraps an evm error when an invalid opcode is encountered.
type ErrInvalidOpCode struct {
	opcode OpCode
}

func (e *ErrInvalidOpCode) Error() string { return fmt.Sprintf("invalid opcode: %s", e.opcode) }
