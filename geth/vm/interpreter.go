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
	"hash"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/math"
	"github.com/ethereum/go-ethereum/log"
)

// Config are the configuration options for the Interpreter
// * 这里是Interpreter的configuration
type Config struct {
	// * 是否开启debug模式，启动geth的时候也有这个选项
	Debug bool // Enables debugging
	// * tracer貌似可以选择不同的版本
	Tracer EVMLogger // Opcode logger
	// ![issue] 不太清楚这里的baseFee指什么，貌似目前的gasPrice与此相关
	NoBaseFee bool // Forces the EIP-1559 baseFee to 0 (needed for 0 price calls)
	// * 启动Keccak SHA3的记录
	// ![issue] 不太清楚这里的preimage指的是什么
	EnablePreimageRecording bool // Enables recording of SHA3/keccak Enables recording of SHA3/keccak preimages

	// * EVM的指令表（instruction table），如果没set则自动补充
	// * 目前是填opcodes？
	JumpTable *JumpTable // EVM instruction table, automatically populated if unset

	// * 填充其他要启动的EIPs
	ExtraEips []int // Additional EIPS that are to be enabled
}

// ScopeContext contains the things that are per-call, such as stack and memory,
// but not transients like pc and gas
// * ScopeContext里面是每次调用都会包含的东西 -> 比如stack和memory
// * 但是pc和gas这种瞬态（transients）没有包含

// ![issue] 只有清楚EVM里面的pc/gas，以及transients，才能对EVM circuit和其他circuits的作用有比较清楚的认识
type ScopeContext struct {
	Memory   *Memory
	Stack    *Stack
	Contract *Contract
}

// keccakState wraps sha3.state. In addition to the usual hash methods, it also supports
// Read to get a variable amount of data from the hash state. Read is faster than Sum
// because it doesn't copy the internal state, but also modifies the internal state.

// * 1.keccakState也封装了sha3.state
// * 2.还支持从hash state里面读取可变变量的数据
// * 3.read比sum更快 -> 它不复制internal state，而且可以修改internal state（那为啥叫read..）
type keccakState interface {
	hash.Hash
	Read([]byte) (int, error)
}

// EVMInterpreter represents an EVM interpreter
// * EVM interpreter（解释器）
type EVMInterpreter struct {
	evm *EVM // * evm.go
	cfg Config

	// ![issue] 并没看懂这两个是什么东西
	hasher    keccakState // Keccak256 hasher instance shared across opcodes
	hasherBuf common.Hash // Keccak256 hasher result array shared aross opcodes

	readOnly   bool   // Whether to throw on stateful modifications
	returnData []byte // Last CALL's return data for subsequent reuse
}

// NewEVMInterpreter returns a new instance of the Interpreter.
// * 返回一个interpreter实例
func NewEVMInterpreter(evm *EVM, cfg Config) *EVMInterpreter {
	// If jump table was not initialised we set the default one.
	// * 这里是一个default的JumpTable，装EVM的指令集？
	if cfg.JumpTable == nil {
		switch {
		case evm.chainRules.IsMerge:
			// * /vm/jump_table.go里面几乎定义了所有的指令集（一组opcode）
			// ! 这玩意有什么作用呢？
			cfg.JumpTable = &mergeInstructionSet
		case evm.chainRules.IsLondon:
			cfg.JumpTable = &londonInstructionSet
		case evm.chainRules.IsBerlin:
			cfg.JumpTable = &berlinInstructionSet
		case evm.chainRules.IsIstanbul:
			cfg.JumpTable = &istanbulInstructionSet
		case evm.chainRules.IsConstantinople:
			cfg.JumpTable = &constantinopleInstructionSet
		case evm.chainRules.IsByzantium:
			cfg.JumpTable = &byzantiumInstructionSet
		case evm.chainRules.IsEIP158:
			cfg.JumpTable = &spuriousDragonInstructionSet
		case evm.chainRules.IsEIP150:
			cfg.JumpTable = &tangerineWhistleInstructionSet
		case evm.chainRules.IsHomestead:
			cfg.JumpTable = &homesteadInstructionSet
		default:
			cfg.JumpTable = &frontierInstructionSet
		}
		for i, eip := range cfg.ExtraEips {
			copy := *cfg.JumpTable
			if err := EnableEIP(eip, &copy); err != nil {
				// Disable it, so caller can check if it's activated or not
				cfg.ExtraEips = append(cfg.ExtraEips[:i], cfg.ExtraEips[i+1:]...)
				log.Error("EIP activation failed", "eip", eip, "error", err)
			}
			cfg.JumpTable = &copy
		}
	}

	// * 返回一个interpreter实例
	// * 如果填了指令集（jumpTable）就直接用，否则返回一个默认的
	return &EVMInterpreter{
		evm: evm,
		cfg: cfg,
	}
}

// Run loops and evaluates the contract's code with the given input data and returns
// the return byte-slice and an error if one occurred.
//
// It's important to note that any errors returned by the interpreter should be
// considered a revert-and-consume-all-gas operation except for
// ErrExecutionReverted which means revert-and-keep-gas-left.

// * 1.运行一个loop，并且用given input data来评估一个contract的code（看看能不能运行？），如果发生错误就返回bytes的slice以及对应的报错
// !   所以调用一笔to null（contract creation）的交易，并且通过input data来构造error，是不错的方法
// * 2.除了`ErrExecutionReverted`以外，其他的大部分错误都是`revert-and-consume-all-gas` -> 所以可以上链，我们能拿到对应的error trace
func (in *EVMInterpreter) Run(contract *Contract, input []byte, readOnly bool) (ret []byte, err error) {
	// Increment the call depth which is restricted to 1024
	// * 增加call depth -> 上限是1024
	in.evm.depth++
	defer func() { in.evm.depth-- }()

	// Make sure the readOnly is only set if we aren't in readOnly yet.
	// This also makes sure that the readOnly flag isn't removed for child calls.
	// * 启动readOnly的config
	if readOnly && !in.readOnly {
		in.readOnly = true
		defer func() { in.readOnly = false }()
	}

	// Reset the previous call's return data. It's unimportant to preserve the old buffer
	// as every returning call will return new data anyway.
	// * 重置returnData -> 不需要保存buffer里面的数据，每次call都会返回新数据
	in.returnData = nil

	// Don't bother with the execution if there's no code.
	// * 没有代码就弹出，不需要执行
	if len(contract.Code) == 0 {
		return nil, nil
	}

	// * 一堆重要的variables
	var (
		// * 这里有可能是执行每一个opcode
		op OpCode // current opcode
		// * returns a new memory model
		mem = NewMemory() // bound memory
		// * 返回当前stackPool中的stack -> 一起传到ScopeContext里，作为call的context
		stack       = newstack() // local stack
		callContext = &ScopeContext{
			Memory:   mem,
			Stack:    stack,
			Contract: contract,
		}
		// For optimisation reason we're using uint64 as the program counter.
		// It's theoretically possible to go above 2^64. The YP defines the PC
		// to be uint256. Practically much less so feasible.
		// * program counter -> 用来计数（OS中常见的组件），具体作用暂不清楚
		pc   = uint64(0) // program counter
		cost uint64
		// copies used by tracer
		pcCopy  uint64 // needed for the deferred EVMLogger
		gasCopy uint64 // for EVMLogger to log gas remaining before execution
		logged  bool   // deferred EVMLogger should ignore already logged steps
		// * opcode执行的结果
		res []byte // result of the opcode execution function
	)
	// Don't move this deferred function, it's placed before the capturestate-deferred method,
	// so that it get's executed _after_: the capturestate needs the stacks before
	// they are returned to the pools
	// * 这个defer函数要放在capturestate-deferred method之前
	// * capturestate貌似需要这里的stack信息
	defer func() {
		returnStack(stack)
	}()
	// * input data
	contract.Input = input

	// * 启动debugger
	if in.cfg.Debug {
		defer func() {
			if err != nil {
				if !logged {
					in.cfg.Tracer.CaptureState(pcCopy, op, gasCopy, cost, callContext, in.returnData, in.evm.depth, err)
				} else {
					in.cfg.Tracer.CaptureFault(pcCopy, op, gasCopy, cost, callContext, in.evm.depth, err)
				}
			}
		}()
	}
	// The Interpreter main run loop (contextual). This loop runs until either an
	// explicit STOP, RETURN or SELFDESTRUCT is executed, an error occurred during
	// the execution of one of the operations or until the done flag is set by the
	// parent context.

	// * 1.这里是interpreter的主循环（main loop）
	// * 2.以下情况会终止执行
	// * 	 1）`STOP`, `RETURN`, `SELFDESTRUCT`的opcode出现，
	// *   2）在执行期间出现了error
	// *	 3）或者parent context设置了`done` flag -> 不清楚这是什么

	// * main loop的循环体
	for {
		// * 应该是debug的一些config
		if in.cfg.Debug {
			// Capture pre-execution values for tracing.
			logged, pcCopy, gasCopy = false, pc, contract.Gas
		}
		// Get the operation from the jump table and validate the stack to ensure there are
		// enough stack items available to perform the operation.
		// * 1.从jump table中拿到operation（应该是opcode）
		// * 2.确保stack有足够的items来执行对应的操作 -> 所以才会有很多stack相关的error，比如overflow和underflow
		op = contract.GetOp(pc)
		operation := in.cfg.JumpTable[op]
		cost = operation.constantGas // For tracing

		// Validate stack
		// * 检测stack是否可用 -> items是否足够
		// * sLen是input data中使用的stack长度，如果长度小于minStack（比如我们前面构造的，就是一个opcode都没有，所以会弹出undeflow）
		// * minStack的数据格式我有点没看懂，minStack(0, 1)
		if sLen := stack.len(); sLen < operation.minStack {
			// ! underflow
			return nil, &ErrStackUnderflow{stackLen: sLen, required: operation.minStack}
		} else if sLen > operation.maxStack {
			// * 所以这里构造的逻辑其实很简单，就是填1025个opcode就可以
			// * 也许有更简单的方法
			// ! 出现Error的位置 - overflow
			return nil, &ErrStackOverflow{stackLen: sLen, limit: operation.maxStack}
		}
		// * 检查gas是否够用
		if !contract.UseGas(cost) {
			return nil, ErrOutOfGas
		}
		if operation.dynamicGas != nil {
			// All ops with a dynamic memory usage also has a dynamic gas cost.
			var memorySize uint64
			// calculate the new memory size and expand the memory to fit
			// the operation
			// Memory check needs to be done prior to evaluating the dynamic gas portion,
			// to detect calculation overflows
			if operation.memorySize != nil {
				memSize, overflow := operation.memorySize(stack)
				if overflow {
					return nil, ErrGasUintOverflow
				}
				// memory is expanded in words of 32 bytes. Gas
				// is also calculated in words.
				if memorySize, overflow = math.SafeMul(toWordSize(memSize), 32); overflow {
					return nil, ErrGasUintOverflow
				}
			}
			// Consume the gas and return an error if not enough gas is available.
			// cost is explicitly set so that the capture state defer method can get the proper cost
			var dynamicCost uint64
			dynamicCost, err = operation.dynamicGas(in.evm, contract, stack, mem, memorySize)
			cost += dynamicCost // for tracing
			if err != nil || !contract.UseGas(dynamicCost) {
				return nil, ErrOutOfGas
			}
			// Do tracing before memory expansion
			if in.cfg.Debug {
				in.cfg.Tracer.CaptureState(pc, op, gasCopy, cost, callContext, in.returnData, in.evm.depth, err)
				logged = true
			}
			if memorySize > 0 {
				mem.Resize(memorySize)
			}
		} else if in.cfg.Debug {
			in.cfg.Tracer.CaptureState(pc, op, gasCopy, cost, callContext, in.returnData, in.evm.depth, err)
			logged = true
		}
		// execute the operation
		res, err = operation.execute(&pc, in, callContext)
		if err != nil {
			break
		}
		pc++
	}

	if err == errStopToken {
		err = nil // clear stop token error
	}

	return res, err
}
