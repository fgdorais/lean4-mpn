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

def main (args : List String) : IO Unit := do
  let ds := [150, 300, 450, 600, 900, 1200]
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
    for d in ds do
      let t ← tm (fromD d) chk s
      IO.println s!"    D={d}: {t/1000}"

end Prof

public def main (args : List String) : IO Unit := Prof.main args
