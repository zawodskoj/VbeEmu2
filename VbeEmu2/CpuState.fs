module CpuState

open System

[<Flags>]
type CpuFlags
    = None      = 0x0000
    | Carry     = 0x0001
    | Parity    = 0x0004
    | Adjust    = 0x0010
    | Zero      = 0x0040
    | Sign      = 0x0080
    | Trap      = 0x0100
    | Interrupt = 0x0200
    | Direction = 0x0400
    | Overflow  = 0x0800

type CpuState = {
    eax: uint32
    ebx: uint32
    ecx: uint32
    edx: uint32
    esp: uint32
    ebp: uint32
    esi: uint32
    edi: uint32

    cs: uint16
    ds: uint16
    es: uint16
    fs: uint16
    gs: uint16
    ss: uint16

    eip: uint32
    eflags: CpuFlags

    memory: byte array
    outs: string list 
}