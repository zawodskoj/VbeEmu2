module Emulator

open CpuState

let peekb seg ofs state =
    let realPtr = int seg * 0x10 + int(uint16 ofs)
    state.memory.[realPtr], state
    
let peekw seg ofs state = 
    let (b1, _) = peekb seg ofs state
    let (b2, _) = peekb seg (ofs + 1u) state
    uint16 b1 ||| (uint16 b2 <<< 8), state

let peekd seg ofs state =
    let (w1, _) = peekw seg ofs state
    let (w2, _) = peekw seg (ofs + 2u) state
    uint32 w1 ||| (uint32 w2 <<< 16), state

let takeNInstrBytes len state : byte list * CpuState =
    [state.eip..state.eip + uint32 len - 1u] 
        |> List.fold (fun (list, state) eip -> peekb state.cs eip state |> fun (byte, _) -> byte::list, {state with eip = state.eip + 1u}) ([], state)
        |> (fun (x, state) -> List.rev x, state)
        
let signExtendByte : byte -> uint32 = sbyte >> int >> uint32
let signExtendWord : uint16 -> uint32 = int16 >> int >> uint32
let signExtendDword = int32 >> int64 >> uint64

let concatAndSignExtend (bytes: byte list) =
    match bytes with
    | [x] -> sbyte x |> int |> uint32
    | [b1; b2] -> uint16 b1 ||| (uint16 b2 <<< 8) |> int16 |> int |> uint32
    | [b1; b2; b3; b4] -> uint32 b1 ||| (uint32 b2 <<< 8) ||| (uint32 b3 <<< 16)  ||| (uint32 b4 <<< 24) 
    | _ -> failwithf "concatAndSignExtend - invalid byte count: %A" bytes

let pokeb seg ofs value state =
    let realPtr = int seg * 0x10 + int(uint16 ofs)
    state.memory.[realPtr] <- value
    state
    
let pokew seg ofs value = pokeb seg ofs (byte value) >> pokeb seg (ofs + 1us) (value >>> 8 |> byte)
let poked seg ofs value = pokew seg ofs (uint16 value) >> pokew seg (ofs + 2us) (value >>> 16 |> uint16)

let pushw value state = 
    //printfn "PUSHW %d" value
    {pokew state.ss (uint16 state.esp - 2us) value state with esp = state.esp - 2u}
let pushd value state = 
    //printfn "PUSHD %d" value
    {poked state.ss (uint16 state.esp - 2us) value state with esp = state.esp - 2u}

let popw state = 
    //printfn "POPW"
    let result, state = peekw state.ss state.esp state
    result, {state with esp = state.esp + 2u}
let popd state =
    //printfn "POPD"
    let result, state = peekd state.ss state.esp state
    result, {state with esp = state.esp + 4u}

type MemrefSize = Byte | Word | Dword
type Register = Ax | Cx | Dx | Bx | Sp | Bp | Si | Di 
type SegRegister = Ss | Cs | Ds | Es | Fs | Gs
type Lvalue
    = Memref of Seg: uint16 * Offset: uint16
    | Regref of Register
    | Segref of SegRegister
type MemrefCompletion = uint32 -> (uint16 * uint16)
type IncompleteMemref
    = Disp16Memref of MemrefCompletion
    | Disp8Memref of MemrefCompletion
    | NoDispMemref of uint16 * uint16
    | NoDispRegref of Register
    
let regFromRegIndex = function 0u -> Ax | 1u -> Cx | 2u -> Dx | 3u -> Bx | 4u -> Sp | 5u -> Bp | 6u -> Si | 7u -> Di
let regrefFromRegIndex = regFromRegIndex >> Regref

let segregFromRegIndex = function 0u -> Es | 1u -> Cs | 2u -> Ss | 3u -> Ds | 4u -> Fs | 5u -> Gs
let segRegrefFromRegIndex = segregFromRegIndex >> Segref

let getValByLvalue lval size state = 
    let sizedVal v = function Byte -> signExtendByte (byte v) | Word -> signExtendWord (uint16 v) | Dword -> v
    let byteH reg = (reg &&& 0xffff00ffu) >>> 8
    match lval, size with
    | Regref Ax, _ -> sizedVal state.eax size, state
    | Regref Cx, _ -> sizedVal state.ecx size, state
    | Regref Dx, _ -> sizedVal state.edx size, state
    | Regref Bx, _ -> sizedVal state.ebx size, state
    | Regref Sp, Byte -> byteH state.eax, state
    | Regref Bp, Byte -> byteH state.ecx, state
    | Regref Si, Byte -> byteH state.edx, state
    | Regref Di, Byte -> byteH state.ebx, state
    | Regref Sp, _ -> sizedVal state.esp size, state
    | Regref Bp, _ -> sizedVal state.ebp size, state
    | Regref Si, _ -> sizedVal state.esi size, state
    | Regref Di, _ -> sizedVal state.edi size, state
    | Segref Es, _ -> signExtendWord state.es, state
    | Segref Cs, _ -> signExtendWord state.cs, state
    | Segref Ss, _ -> signExtendWord state.ss, state
    | Segref Ds, _ -> signExtendWord state.ds, state
    | Segref Fs, _ -> signExtendWord state.fs, state
    | Segref Gs, _ -> signExtendWord state.gs, state
    | Memref(seg, ofs), _ -> sizedVal (peekd seg (uint32 ofs) state |> fst) size, state

let setValToLvalue lval size value state = 
    let changeReg reg value = 
        function 
        | Byte -> (reg &&& 0xffffff00u) ||| (value &&& 0xffu) 
        | Word -> (reg &&& 0xffff0000u) ||| (value &&& 0xffffu) 
        | Dword -> value
    let changeRegH reg value = (reg &&& 0xffff00ffu) ||| ((value &&& 0xffu) <<< 8)
    match lval, size with
    | Regref Ax, _ -> { state with eax = changeReg state.eax value size }
    | Regref Cx, _ -> { state with ecx = changeReg state.ecx value size }
    | Regref Dx, _ -> { state with edx = changeReg state.edx value size }
    | Regref Bx, _ -> { state with ebx = changeReg state.ebx value size }
    | Regref Sp, Byte -> { state with eax = changeRegH state.eax value }
    | Regref Bp, Byte -> { state with ecx = changeRegH state.ecx value }
    | Regref Si, Byte -> { state with edx = changeRegH state.edx value }
    | Regref Di, Byte -> { state with ebx = changeRegH state.ebx value }
    | Regref Sp, _ ->  { state with esp = changeReg state.esp value size }
    | Regref Bp, _ ->  { state with ebp = changeReg state.ebp value size }
    | Regref Si, _ ->  { state with esi = changeReg state.esi value size }
    | Regref Di, _ ->  { state with edi = changeReg state.edi value size }
    | Segref Es, _ -> { state with es = uint16 value }
    | Segref Cs, _ -> { state with cs = uint16 value }
    | Segref Ss, _ -> { state with ss = uint16 value }
    | Segref Ds, _ -> { state with ds = uint16 value }
    | Segref Fs, _ -> { state with fs = uint16 value }
    | Segref Gs, _ -> { state with gs = uint16 value }
    | Memref(seg, ofs), _ -> 
        let prev = peekd seg (uint32 ofs) state |> fst
        poked seg ofs (changeReg prev value size) state

// (>>>) value >> (&&&) 1u >> (^^^)
let calcParity value = [0..31] |> List.fold (fun v bit -> ((value >>> bit) &&& 1u) ^^^ v) 0u = 0u

let alu size lval reg immediate state =
    let anyFlags = CpuFlags.Carry ||| CpuFlags.Parity ||| CpuFlags.Overflow ||| CpuFlags.Sign ||| CpuFlags.Zero ||| CpuFlags.Adjust
    let adjustFlags (result: uint64) allowedFlags resetFlags state =
        let tr = result |> uint32
        let sf = if tr |> int < 0 then CpuFlags.Sign else CpuFlags.None
        let zf = if tr = 0u then CpuFlags.Zero else CpuFlags.None
        let pf = if calcParity tr then CpuFlags.Parity else CpuFlags.None
        let cf = if result &&& (1UL <<< 32) > 0UL then CpuFlags.Carry else CpuFlags.None
        let ofl = if (result &&& (1UL <<< 33) > 0UL) <> (tr |> int < 0) then CpuFlags.Overflow else CpuFlags.None
        let nflags = ((sf ||| zf ||| pf ||| cf ||| ofl) &&& allowedFlags) ||| (state.eflags &&& ~~~(allowedFlags ||| resetFlags))
        { state with eflags = nflags }

    let immutableOp op allowedFlags resetFlags =
        let (lhs, state) = getValByLvalue lval size state
        let result = op (signExtendDword lhs) (signExtendDword immediate)
        result, adjustFlags result allowedFlags resetFlags state
    let mutableOp op allowedFlags resetFlags = 
        let (result, state) = immutableOp op allowedFlags resetFlags
        setValToLvalue lval size (uint32 result) state
    let bitOp op = mutableOp op (CpuFlags.Sign ||| CpuFlags.Zero ||| CpuFlags.Parity) (CpuFlags.Overflow ||| CpuFlags.Carry)
    match reg with
    | 0u -> mutableOp (+) anyFlags CpuFlags.None
    | 1u -> bitOp (|||)
    | 2u -> mutableOp ((+) (if state.eflags.HasFlag(CpuFlags.Carry) then 1UL else 0UL) >> (+)) anyFlags CpuFlags.None
    | 5u -> mutableOp ((-) (if state.eflags.HasFlag(CpuFlags.Carry) then 1UL else 0UL) >> (-)) anyFlags CpuFlags.None
    | 4u -> bitOp (&&&)
    | 5u -> mutableOp (-) anyFlags CpuFlags.None
    | 6u -> bitOp (^^^)
    | 7u -> immutableOp (-) anyFlags CpuFlags.None |> snd
    | x -> failwithf "invalid reg value: %d" x
    
let alu2 size lval reg immediate state =
    let anyFlags = CpuFlags.Carry ||| CpuFlags.Parity ||| CpuFlags.Overflow ||| CpuFlags.Sign ||| CpuFlags.Zero ||| CpuFlags.Adjust
    let adjustFlags (result: uint64) allowedFlags resetFlags state =
        let tr = result |> uint32
        let sf = if tr |> int < 0 then CpuFlags.Sign else CpuFlags.None
        let zf = if tr = 0u then CpuFlags.Zero else CpuFlags.None
        let pf = if calcParity tr then CpuFlags.Parity else CpuFlags.None
        let cf = if result &&& (1UL <<< 32) > 0UL then CpuFlags.Carry else CpuFlags.None
        let ofl = if (result &&& (1UL <<< 33) > 0UL) <> (tr |> int < 0) then CpuFlags.Overflow else CpuFlags.None
        let nflags = ((sf ||| zf ||| pf ||| cf ||| ofl) &&& allowedFlags) ||| (state.eflags &&& ~~~(allowedFlags ||| resetFlags))
        { state with eflags = nflags }

    let immutableOp op allowedFlags resetFlags =
        let (lhs, state) = getValByLvalue lval size state
        let result = op (signExtendDword lhs) (signExtendDword immediate)
        result, adjustFlags result allowedFlags resetFlags state
    let mutableOp op allowedFlags resetFlags = 
        let (result, state) = immutableOp op allowedFlags resetFlags
        setValToLvalue lval size (uint32 result) state
    let bitOp op = mutableOp op (CpuFlags.Sign ||| CpuFlags.Zero ||| CpuFlags.Parity) (CpuFlags.Overflow ||| CpuFlags.Carry)
    match reg with
    | 4u -> mutableOp (fun x y -> x <<< int y) anyFlags CpuFlags.None
    | 5u -> mutableOp (fun x y -> x >>> int y) anyFlags CpuFlags.None
    | x -> failwithf "invalid reg value: %d" x
    
let executeSingleOp state =
    printf "%04x:%04x " state.cs state.eip
    let oprintfn = printf
    let BYTE = -1
    let WORD = -2
    let DWRD = -4
    let MODRM = -10
    let (|Sequence|_|) seq state =
        let cont = -228
        let propagatedSeq = seq |> List.collect (function x when x = WORD -> [WORD; cont] | x when x = DWRD -> [DWRD; cont; cont; cont] | x -> [x])
        let (equalLenSeq, state) = takeNInstrBytes (List.length propagatedSeq) state
        let zipped = List.zip propagatedSeq equalLenSeq
        if List.fold (&&) true (zipped |> List.map (fun (a, b) -> a < 0 || byte a = b))
            then
                let patternPts = propagatedSeq |> List.indexed |> List.filter (fun (_, x) -> x < 0 && x <> cont)
                (patternPts |> List.map (fun (pos, sz) -> equalLenSeq |> List.skip pos |> List.take (-sz) |> concatAndSignExtend), state) |> Some
            else None
    let (|Lvalue|_|) seg modrm = 
        let reg = (modrm &&& 0x38u) >>> 3
        let modv = modrm &&& 0xc0u
        let wrapper = 
            match modv with 
            | 0u -> fun adr -> NoDispMemref(seg, adr)
            | 0x40u -> fun adr -> Disp8Memref(fun disp8 -> seg, adr + uint16 disp8)
            | 0x80u -> fun adr -> Disp16Memref(fun disp8 -> seg, adr + uint16 disp8)
            | 0xc0u -> fun _ -> failwith "wrapper with 0xc0 modv is not allowed"
        match modv, modrm &&& 7u with
        | 0xc0u, rm -> Some(NoDispRegref ([|Ax; Cx; Dx; Bx; Sp; Bp; Si; Di|].[int rm]), reg)
        | 0u, 6u -> Some(Disp16Memref(fun disp16 -> seg, uint16 disp16), reg)
        | _, 0u -> Some(wrapper(uint16 state.ebx + uint16 state.esi), reg)
        | _, 1u -> Some(wrapper(uint16 state.ebx + uint16 state.edi), reg)
        | _, 2u -> Some(wrapper(uint16 state.ebp + uint16 state.esi), reg)
        | _, 3u -> Some(wrapper(uint16 state.ebp + uint16 state.edi), reg)
        | _, 4u -> Some(wrapper(uint16 state.esi), reg)
        | _, 5u -> Some(wrapper(uint16 state.edi), reg)
        | _, 6u -> Some(wrapper(uint16 state.ebp), reg)
        | _, 7u -> Some(wrapper(uint16 state.ebx), reg)
    let (|InRange|_|) fromv tov value = 
        let value = value &&& 0xffu
        if value >= fromv && value <= tov then Some value else None
    let (|Modrm16Sequence|_|) seq seg state =
        if seq |> List.filter ((=) MODRM) |> List.length <> 1 then failwith "invalid sequence"
        let origSeq = seq
        let seq = List.takeWhile (fun x -> x <> MODRM) seq @ [MODRM]
        let _::seqRest = List.skipWhile (fun x -> x <> MODRM) origSeq
        let replacedSeq = seq |> List.map (fun x -> if x = MODRM then BYTE else x)
        match state with
        | Sequence replacedSeq (parsed, nstate) ->
            let modrmIx = seq |> List.where (fun x -> x < 0) |> List.findIndex ((=) MODRM)
            let modrmByte = parsed |> List.item modrmIx
            let head = List.take modrmIx parsed
            let rest dispBytes = 
                let truncatedSeq = List.takeWhile (fun x -> x <> MODRM) origSeq
                let seq = truncatedSeq @ (byte >> int) modrmByte::seqRest @ List.map (byte >> int) dispBytes
                match state with Sequence seq result -> result
            match modrmByte with
            | Lvalue seg (NoDispRegref(regref), reg) -> 
                let rest, state = rest []
                Some(Regref(regref), reg, head @ rest, state)
            | Lvalue seg (NoDispMemref(seg, ofs), reg) ->
                let rest, state = rest []
                Some(Memref(seg, ofs), reg, head @ rest, state)
            | Lvalue seg (Disp8Memref(fn), reg) -> 
                let disp8, _ = peekb nstate.cs nstate.eip nstate
                let rest, state = rest [disp8]
                Some(Memref(fn <| uint32 disp8), reg, head @ rest, state)
            | Lvalue seg (Disp16Memref(fn), reg) -> 
                let disp16a, nstate = peekb nstate.cs nstate.eip nstate
                let disp16b, _ = peekb nstate.cs (nstate.eip + 1u) nstate
                let rest, state = rest [disp16a; disp16b]
                Some(Memref(fn <| (uint32 disp16a ||| (uint32 disp16b <<< 8))), reg, head @ rest, state)
            | _ -> None
        | _ -> None
    let (|DsModrm16Sequence|_|) seq = function Modrm16Sequence seq state.ds result -> Some result | _ -> None
    let (|CsModrm16Sequence|_|) seq = function Modrm16Sequence seq state.cs result -> Some result | _ -> None
    match state with
    | Sequence [0x9c] ([], state) -> // PUSHF
        oprintfn "PUSHF esp: %x" state.esp
        false, pushw (uint16 state.eflags) state
    | Sequence [0x9d] ([], state) -> // POPF
        oprintfn "POPF esp: %x" state.esp
        let result, state = popw state
        false, { state with eflags = System.Enum.ToObject(typeof<CpuFlags>, result) :?> CpuFlags }
    | DsModrm16Sequence [0x80; MODRM; BYTE] (ref, reg, [imm8], state) -> // ALU r/m8, imm8
        oprintfn "ALU r/m8, 0x%x" (uint8 imm8)
        false, alu Byte ref reg (signExtendByte <| byte imm8) state
    | DsModrm16Sequence [0x81; MODRM; WORD] (ref, reg, [imm16], state) -> // ALU r/m16, imm16
        oprintfn "ALU r/m16, 0x%x" (uint16 imm16)
        false, alu Byte ref reg (signExtendWord <| uint16 imm16) state
    | DsModrm16Sequence [0x83; MODRM; BYTE] (ref, reg, [imm8], state) -> // ALU r/m16, imm8
        oprintfn "ALU r/m16, 0x%x" (uint8 imm8)
        false, alu Word ref reg (signExtendByte <| uint8 imm8) state
    | DsModrm16Sequence [0x85; MODRM] (ref, reg, [], state) -> // TEST r/m16, r16
        oprintfn "TEST r/m16, %O" <| regrefFromRegIndex reg
        let tstate = alu Word ref 4u (getValByLvalue (regrefFromRegIndex reg) Word state |> fst) state
        false, { state with eflags = tstate.eflags }
    | DsModrm16Sequence [0xD0; MODRM] (ref, reg, [], state) -> // ALU2 r/m8, 1
        oprintfn "ALU2 r/m8, 1"
        false, alu2 Byte ref reg 1u state
    | DsModrm16Sequence [0xD1; MODRM] (ref, reg, [], state) -> // ALU2 r/m16, 1
        oprintfn "ALU2 r/m16, 1"
        false, alu2 Byte ref reg 1u state
    | DsModrm16Sequence [0xD3; MODRM] (ref, reg, [], state) -> // ALU2 r/m16, CL
        oprintfn "ALU2 r/m16, CL"
        false, alu2 Byte ref reg (getValByLvalue (Regref Cx) Byte state |> fst) state
    | Sequence [0x0C; BYTE] ([imm8], state) -> // OR AL, imm8
        oprintfn "OR AX, 0x%x" (uint8 imm8)
        false, alu Byte (Regref Ax) 1u (signExtendByte (uint8 imm8)) state
    | Sequence [0x2C; BYTE] ([imm8], state) -> // SUB AL, imm8
        oprintfn "SUB AX, 0x%x" (uint8 imm8)
        false, alu Byte (Regref Ax) 5u (signExtendByte (uint8 imm8)) state
    | DsModrm16Sequence [0x31; MODRM] (ref, reg, [], state) -> // XOR r/m16, r16
        oprintfn "XOR r/m16, r16"
        false, alu Word ref 6u (getValByLvalue (regrefFromRegIndex reg) Word state |> fst) state
    | DsModrm16Sequence [0x3A; MODRM] (ref, reg, [], state) -> // CMP r8, r/m8
        oprintfn "CMP r8, r/m8"
        false, alu Byte (regrefFromRegIndex reg) 7u (getValByLvalue ref Byte state |> fst) state
    | Sequence [0x3C; BYTE] ([imm8], state) -> // CMP AL, imm8
        oprintfn "CMP AX, 0x%x" (uint8 imm8)
        false, alu Byte (Regref Ax) 7u (signExtendByte (uint8 imm8)) state
    | Sequence [0x3D; WORD] ([imm16], state) -> // CMP AX, imm16
        oprintfn "CMP AX, 0x%x" (uint16 imm16)
        false, alu Word (Regref Ax) 7u (signExtendWord (uint16 imm16)) state
    | Sequence [0x72; BYTE] ([rel8], state) -> // JC rel8
        oprintfn "JC 0x%04x" (state.eip + signExtendByte (byte rel8) |> int)
        if state.eflags.HasFlag(CpuFlags.Carry) 
            then false, { state with eip = state.eip + signExtendByte (byte rel8) }
            else false, state
    | Sequence [0x74; BYTE] ([rel8], state) -> // JZ rel8
        oprintfn "JZ 0x%04x" (state.eip + signExtendByte (byte rel8) |> int)
        if state.eflags.HasFlag(CpuFlags.Zero) 
            then false, { state with eip = state.eip + signExtendByte (byte rel8) }
            else false, state
    | Sequence [0x75; BYTE] ([rel8], state) -> // JNZ rel8
        oprintfn "JNZ 0x%04x" (state.eip + signExtendByte (byte rel8) |> int)
        if not <| state.eflags.HasFlag(CpuFlags.Zero) 
            then false, { state with eip = state.eip + signExtendByte (byte rel8) }
            else false, state
    | Sequence [0x76; BYTE] ([rel8], state) -> // JNA rel8
        oprintfn "JNA 0x%04x" (state.eip + signExtendByte (byte rel8) |> int)
        if (state.eflags.HasFlag(CpuFlags.Carry)) || (state.eflags.HasFlag(CpuFlags.Zero))
            then false, { state with eip = state.eip + signExtendByte (byte rel8) }
            else false, state
    | Sequence [0x77; BYTE] ([rel8], state) -> // JA rel8
        oprintfn "JA 0x%04x" (state.eip + signExtendByte (byte rel8) |> int)
        if not (state.eflags.HasFlag(CpuFlags.Carry)) && not (state.eflags.HasFlag(CpuFlags.Zero))
            then false, { state with eip = state.eip + signExtendByte (byte rel8) }
            else false, state
    | Sequence [0x7C; BYTE] ([rel8], state) -> // JL rel8
        oprintfn "JL 0x%04x" (state.eip + signExtendByte (byte rel8) |> int)
        if state.eflags.HasFlag(CpuFlags.Carry) <> state.eflags.HasFlag(CpuFlags.Overflow)
            then false, { state with eip = state.eip + signExtendByte (byte rel8) }
            else false, state
    | Sequence [0x06] ([], state) -> // PUSH ES
        oprintfn "PUSH ES esp: %x" state.esp
        false, pushw state.es state
    | Sequence [0x07] ([], state) -> // POP ES
        oprintfn "POP ES esp: %x" state.esp
        let value, state = popw state
        false, { state with es = value }
    | Sequence [0x1e] ([], state) -> // PUSH DS
        oprintfn "PUSH DS esp: %x" state.esp
        false, pushw state.ds state
    | Sequence [0x1f] ([], state) -> // POP DS
        oprintfn "POP DS esp: %x" efstate.esp
        let value, state = popw state
        false, { state with ds = value }
    | Sequence [BYTE] ([InRange 0x40u 0x47u movr], state) -> // INC r16
        let ref = regrefFromRegIndex (movr - 0x40u)
        oprintfn "INC %O" ref
        false, setValToLvalue ref Word (1u + fst (getValByLvalue ref Word state)) state
    | Sequence [BYTE] ([InRange 0x48u 0x4fu movr], state) -> // DEC r16
        let ref = regrefFromRegIndex (movr - 0x48u)
        oprintfn "DEC %O" ref
        false, setValToLvalue ref Word (fst (getValByLvalue ref Word state) - 1u) state
    | Sequence [BYTE] ([InRange 0x50u 0x57u movr], state) -> // PUSH r16
        let ref = regrefFromRegIndex (movr - 0x50u)
        oprintfn "PUSH %O esp: %x" ref state.esp
        false, pushw (fst >> uint16 <| getValByLvalue ref Word state) state
    | Sequence [BYTE] ([InRange 0x58u 0x5fu movr], state) -> // POP r16
        let ref = regrefFromRegIndex (movr - 0x58u)
        oprintfn "POP %O esp: %x" ref state.esp
        let value, state = popw state
        false, setValToLvalue ref Word (signExtendWord value) state
    | Sequence [0x60] ([], state) -> // PUSHAW
        oprintfn "PUSHAW esp: %x" state.esp
        false, state |> (
            pushw (uint16 state.eax) >> 
            pushw (uint16 state.ecx) >> 
            pushw (uint16 state.edx) >> 
            pushw (uint16 state.ebx) >> 
            pushw (uint16 state.esp) >> 
            pushw (uint16 state.ebp) >> 
            pushw (uint16 state.esi) >> 
            pushw (uint16 state.edi))
    | Sequence [0x61] ([], state) -> // POPAW
        oprintfn "POPAW esp: %x" state.esp
        let r, state = popw state
        let r, state = popw { state with edi = uint32 r }
        let r, state = popw { state with esi = uint32 r }
        let _, state = popw { state with ebp = uint32 r }
        let r, state = popw state
        let r, state = popw { state with ebx = uint32 r }
        let r, state = popw { state with edx = uint32 r }
        let r, state = popw { state with ecx = uint32 r }
        false, { state with eax = uint32 r }
    | Sequence [0x24; BYTE] ([imm8], state) -> // AND AL, imm8
        oprintfn "AND AL, %x" (uint8 imm8)
        false, alu Byte (Regref Ax) 4u (uint8 >> signExtendByte <| imm8) state
    | Sequence [0x2d; WORD] ([imm16], state) -> // SUB AX, imm16
        oprintfn "SUB AX, 0x%x" (uint16 imm16)
        false, alu Word (Regref Ax) 5u (uint16 >> signExtendWord <| imm16) state
    | DsModrm16Sequence [0x30; MODRM] (ref, reg, [], state) -> // XOR r/m8, r8
        oprintfn "XOR r/m8, %O" reg
        false, alu Byte ref 6u (getValByLvalue (regrefFromRegIndex reg) Byte state |> fst) state
    | DsModrm16Sequence [0x88; MODRM] (ref, reg, [], state) -> // MOV r/m8, r8
        oprintfn "MOV r/m8, %O" reg
        false, setValToLvalue ref Byte (getValByLvalue (regrefFromRegIndex reg) Byte state |> fst) state
    | DsModrm16Sequence [0x89; MODRM] (ref, reg, [], state) ->  // MOV r/m16, r16
        oprintfn "MOV r/m16, %O" reg
        false, setValToLvalue ref Word (getValByLvalue (regrefFromRegIndex reg) Word state |> fst) state
    | DsModrm16Sequence [0x8a; MODRM] (ref, reg, [], state) -> // MOV r8, r/m8
        oprintfn "MOV %O, r/m8" reg
        false, setValToLvalue (regrefFromRegIndex reg) Byte (getValByLvalue ref Byte state |> fst) state
    | DsModrm16Sequence [0x8b; MODRM] (ref, reg, [], state) -> // MOV r16, r/m16
        oprintfn "MOV %O, r/m16" reg
        false, setValToLvalue (regrefFromRegIndex reg) Word (getValByLvalue ref Word state |> fst) state
    | DsModrm16Sequence [0x8e; MODRM] (ref, reg, [], state) -> // MOV sreg, r/m16
        oprintfn "MOV %O, r/m16" <| segRegrefFromRegIndex reg
        false, setValToLvalue (segRegrefFromRegIndex reg) Word (getValByLvalue ref Word state |> fst) state
    | Sequence [0xc3] ([], state) -> // RET
        oprintfn "RET"
        let ip, state = popw state
        false, { state with eip = uint32 ip }
    | Sequence [0xcf] ([], state) -> // IRET
        true, state
    | Sequence [0xe8; WORD] ([rel16], state) -> // CALL rel16
        oprintfn "CALL 0x%04x relv: %x esp: %x" (state.eip + signExtendWord (uint16 rel16) |> int) rel16 state.esp
        let state = pushw (uint16 state.eip) state
        false, { state with eip = state.eip + signExtendWord (uint16 rel16) }
    | Sequence [0xe9; WORD] ([rel16], state) -> // JMP rel16
        oprintfn "JMP 0x%04x" (state.eip + signExtendWord (uint16 rel16) |> int)
        false, { state with eip = state.eip + signExtendWord (uint16 rel16) }
    | Sequence [0xeb; BYTE] ([rel8], state) -> // JMP rel8
        oprintfn "JMP 0x%04x" (state.eip + signExtendByte (uint8 rel8) |> int)
        false, { state with eip = state.eip + signExtendByte (uint8 rel8) }
    | Sequence [0xef] ([], state) -> // OUT DX, AL
        oprintfn "OUT %x, AL(%x)" (uint16 state.edx) (uint8 state.eax)
        false, { state with outs = sprintf "OUT %x, AL(%x)" (uint16 state.edx) (uint8 state.eax) :: state.outs }
    | Sequence [BYTE; BYTE] ([InRange 0xb0u 0xb7u movr; imm8], state) -> // MOV r8, imm8
        oprintfn "MOV %O, 0x%x" <| regrefFromRegIndex (movr - 0xb0u) <| uint8 imm8
        false, setValToLvalue (regrefFromRegIndex (movr - 0xb0u)) Byte imm8 state
    | Sequence [BYTE; WORD] ([InRange 0xb8u 0xbfu movr; imm16], state) -> // MOV r16, imm16
        oprintfn "MOV %O, 0x%x" <| regrefFromRegIndex (movr - 0xb8u) <| uint16 imm16
        false, setValToLvalue (regrefFromRegIndex (movr - 0xb8u)) Word imm16 state
    | CsModrm16Sequence [0x2e; 0xff; MODRM] (ref, _, [], state) -> // JMP CS:r/m16
        oprintfn "JMP CS:r/m16"
        let ip, state = getValByLvalue ref Word state
        false, { state with eip = ip }
    | Sequence [BYTE; BYTE] ([x; y], _) -> failwithf "Invalid opcode: %x %x" x y
    | _ -> failwithf "Very invalid opcode (don't know byte)"

let runEmulator state =
    let rec runEmulator' state nx =
        let brks = [0x3cc2us; 0x3ce9us]
        let (gotIret, state) = if nx then false, state else executeSingleOp state
        printf "\n"
        if gotIret then
            printfn "got iret"
            printfn "total outs: %A" state.outs
            while true do ()
        if brks |> List.contains (uint16 state.eip) then
            printfn "got brkp"
            printf "%O" { state with memory = null }
        (*match System.Console.ReadLine().Trim() with
        | "" | "s" -> runEmulator' state false
        | "reg" ->
            printfn "%O" { state with memory = null }
            runEmulator' state true
        | x ->
            printfn "invalid operation: %s" x
            runEmulator' state true*)
        runEmulator' state false
    runEmulator' state false