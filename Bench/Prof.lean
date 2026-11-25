module

import MPN64
import Bench.Harness
import Tune.Harness

open ScalarArray MPN MPN.W64

namespace Prof

def chk (a : UInt64Array) : UInt64 := a.size.toUInt64 + a.getD 0 0

def tm {α β : Type} (f : α → β) (c : β → UInt64) (a : α) : IO Float := do
  let t ← Bench.time (fun x (_ : α) => f x) c a a
  return t.median

def fromD (D : Nat) (s : String) : UInt64Array :=
  ops64.fromDec (DecChunks.parseBase id s) D s.utf8ByteSize



def mulIn (arr : UInt64Array) (n : USize) (x c : UInt64) : UInt64Array :=
  if h : n.toNat ≤ arr.size ∧ n.toNat < USize.size then
    MPN.WordFolds.foldThen n (fun _ _ z c => MPN.WordArray.mulAdd2 (A := UInt64Array) z x 0 c) arr 0
      ⟨by simpa [MPN.LimbArray.size] using h.1, by simpa using h.2⟩ 0 c (fun arr _ _ => arr)
  else arr

def readBIp (s : String) (stop i : Nat) (arr : UInt64Array) (u : USize) (c : UInt64) (cnt : UInt32) :
    UInt64Array :=
  if h : i < stop ∧ i < s.utf8ByteSize then
    let b := s.getUTF8Byte ⟨i⟩ h.2
    let v := c * 10 + (b.toUInt64 - 48)
    if cnt + 1 = 19 then
      let arr := mulIn arr (u + 1) 10000000000000000000 v
      let u := if arr.getD u.toNat 0 != 0 then u + 1 else u
      readBIp s stop (i + 1) arr u 0 0
    else readBIp s stop (i + 1) arr u v (cnt + 1)
  else
    let arr := if cnt = 0 then arr else mulIn arr (u + 1) (dec64.pow10 cnt.toNat) c
    trimA arr
termination_by stop - i

def one (which : String) (n : Nat) : IO Unit := do
  let a : UInt64Array := Tune.sample n 7
  let s := Num.toDecimal a
  let mut acc : UInt64 := 0
  for _ in [0:20] do
    let r := match which with
      | "proto" => readBIp s s.utf8ByteSize 0 (UInt64Array.replicate (s.utf8ByteSize / 19 + 2) 0) 0 0 0
      | "readBI" => DecChunks.readBI (O := dec64) s s.utf8ByteSize 0 (UInt64Array.replicate (s.utf8ByteSize / 19 + 2) 0) 0 0 0
      | "full" => (Num.ofDecimal? s).getD (UInt64Array.replicate 1 0)
      | _ => UInt64Array.replicate 1 0
    acc := acc + chk r
  IO.println s!"{acc}"

def main (args : List String) : IO Unit := do
  if args.head? == some "one" then
    one args[1]! args[2]!.toNat!
    return
  let ds := [300, 600, 1200, 2400]
  let sizes := if args.isEmpty then [64, 128, 256, 512, 1024, 2048, 4096] else args.map String.toNat!
  for n in sizes do
    let a : UInt64Array := Tune.sample n 7
    let s := Num.toDecimal a
    let L := Nat.log2 s.utf8ByteSize + 1
    let ok := (fromD 300 s).toNat == a.toNat && (Num.ofDecimal? s).map (·.toNat) == some a.toNat
    let full ← tm Num.ofDecimal? (fun o => (o.map chk).getD 0) s
    let gmp ← tm Bench.Mpn.setStr (fun x => x.toUInt64) s
    let isn ← tm isNatB (fun b => if b then 1 else 0) s
    let pows ← tm (fun (k : Nat) => ops64.powsZ k) (fun l => l.length.toUInt64) L
    let base ← tm (fun s => ofDecimalWith 1000000000 s) (fun o => (o.map chk).getD 0) s
    let dc ← tm (fun s => ofDecimalWith 0 s) (fun o => (o.map chk).getD 0) s
    IO.println s!"{n} {ok}: full {full/1000} us, gmp {gmp/1000} ({full/gmp}x), base {base/1000} ({base/gmp}x) dc {dc/1000} ({dc/gmp}x); isNat {isn/1000} pows {pows/1000}"
    let rb ← tm (fun s => DecChunks.readBI (O := dec64) s s.utf8ByteSize 0 (UInt64Array.replicate (s.utf8ByteSize / 19 + 2) 0) 0 0 0) chk s
    let rp ← tm (fun s => readBIp s s.utf8ByteSize 0 (UInt64Array.replicate (s.utf8ByteSize / 19 + 2) 0) 0 0 0) chk s
    IO.println s!"  proto alone {rp/1000} ({rp/gmp}x)"
    IO.println s!"  readBI alone {rb/1000} ({rb/gmp}x)"
    for d in ds do
      let t ← tm (fromD d) chk s
      IO.println s!"    D={d}: {t/1000}"

end Prof

public def main (args : List String) : IO Unit := Prof.main args
