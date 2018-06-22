open System
open System.IO
open Emulator
open CpuState

let memsz = 0x100000 // megabyte

//let file = File.OpenRead("C:\\Users\\zawod\\bochs\\vesabios.bin")
//let loadAt = 0xc0000
//let initEip = 0x151u
//let initCs = 0xc000us

let file = File.OpenRead("C:\\Users\\zawod\\bochs\\conventional.bin")
let loadAt = 0
let initEip = 0x151u
let initCs = 0xc000us

let memory = Array.zeroCreate<byte> memsz
file.Read(memory, loadAt, int file.Length) |> ignore

let state = {
    eax = 0x3u; ebx = 0u; ecx = 0u; edx = 0u
    esp = 0xfffcu; ebp = 0u; esi = 0u; edi = 0u

    cs = initCs; ss = 0x8000us; ds = 0x7000us; es = 0us; fs = 0us; gs = 0us

    eip = initEip; eflags = CpuFlags(); memory = memory; outs = []
}

state |> runEmulator |> ignore