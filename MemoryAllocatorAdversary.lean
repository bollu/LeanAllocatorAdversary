import Lean
open Lean

/-- type that is 4(n + 1) bytes long. -/
@[reducible, simp]
def Data : Nat → Type
| 0 => Int
| n + 1 => Int × Data n

set_option trace.Compiler.result true in
/-- default value of [42, 43, 44, ...] repeated (n + 1) times. -/
instance : Inhabited (Data n) where
  default := go n
  where
   go : (n : Nat) → Data n
   | 0 => 42
   | n' + 1 => (42, go n')

/-
cases x.1 : lcErased
| Nat.zero =>
  let _x.2 := 42;
  let _x.3 := Int.ofNat _x.2;
  return _x.3
| Nat.succ n.4 =>
  let _x.5 := 42;
  let _x.6 := Int.ofNat _x.5;
  let _x.7 := instInhabitedData.go n.4;
  let _x.8 := Prod.mk _ _ _x.6 _x.7;
  return _x.8 
-/

/-- print to string. -/
instance : ToString (Data n) where
  toString x := go n x
  where
   go : (n : Nat) → Data n → String
   | 0, i => s!"{i}"
   | n' + 1, (i, is) => s!"({i}, {go n' is})"

/-- Make a piece of data. -/
def Data.mk (n : Nat) : Data n := default

/-- Linked List of `Data`. -/
inductive LinkedList where
| Nil : LinkedList
| Cons (d : Array Nat) (next : LinkedList) : LinkedList

/-- to string -/
def LinkedList.toString : LinkedList → String
| Nil => "nil"
| Cons x xs => s!"({x} {xs.toString})"

/-- typeclass instance -/
instance : ToString LinkedList where toString := LinkedList.toString

def LinkedList.mkFromSizeLen (σ : Nat) (len : Nat) : LinkedList :=
  match len with
  | 0 => .Nil
  | len'+1 => .Cons (Array.mkArray (n := len) (v := σ)) (mkFromSizeLen σ len')


/-- keep every node with index `i` such that `i % k == 0` -/
def LinkedList.keepEvery (n : Nat) : LinkedList → LinkedList :=
  go n 0
  where
    go (n : Nat) (i: Nat) : LinkedList → LinkedList
    | .Nil => .Nil
    | .Cons d next =>
      let next' := go n (i + 1) next
      if i % n == 0 then .Cons d next' else next'

/-- drop `n` nodes -/
def LinkedList.drop : Nat → LinkedList → LinkedList
| 0, xs => xs
| _, Nil => Nil
| n+1, Cons _x xs => xs.drop n

/-- allocator structure: for each object size, have a list of pages. -/

-- https://github.com/leanprover/lean4/blob/3aa1cfcceabf7d091a3b2e5d4330df76767336ac/src/runtime/alloc.cpp#L25C37-L25C37
def lean_page_size : Nat := 8192

-- https://github.com/leanprover/lean4/blob/3aa1cfcceabf7d091a3b2e5d4330df76767336ac/stage0/src/include/lean/lean.h#L25-L26
def max_small_object_size : Nat := 4196
def lean_size_delta : Nat := 8

def lean_num_objects_in_page : Nat := lean_page_size / lean_size_delta
#eval lean_num_objects_in_page

-- over 9000!
def n_replicated : Nat :=  9001

/-- TODO: actually diagonalize this: 1st element from 1st list and so on. -/
def diagonalizePrintLists (lists : HashMap Nat LinkedList) : IO Unit := do {
  let _ ← lists.foldM (init := (0 : Nat))
    -- drop k elements from the list and print it.
    fun ix _k list => do IO.println (list.drop ix); pure (ix + 1);
  pure ();
}

def max_size_explored : Nat := max_small_object_size / lean_size_delta 
#eval max_size_explored -- 524
  
def nanosToMillis (nanos : Nat) : Float := 
  (Float.ofNat nanos) / (1e6 : Float)

def timeDeltaMsString (tNanosNew tNanosOld : Nat) : String := 
  let tNanosDelta := tNanosNew - tNanosOld
  let tMillisDelta := nanosToMillis tNanosDelta
  s!"{tMillisDelta}ms"


def get_rss : IO Nat := do 
  let f ← IO.FS.readFile "/proc/self/stat"
  let spaced := f.splitOn " ";
  -- https://man7.org/linux/man-pages/man5/proc.5.html
  return spaced[24 - 1]!.toNat!


-- https://man7.org/linux/man-pages/man2/getpagesize.2.html
@[extern "lean_get_page_size"]
def get_page_size : IO UInt32 := default

-- # of bytes we are retaining.
-- Off by the boxing/pointers
def needUse (cur_size : Nat) : Nat := 
match cur_size with
 | 0 => 0
 | .succ cur_size' => 
    obj_size*num_kept + needUse cur_size' where
      num_per_page := (lean_page_size/obj_size)
      num_kept := n_replicated/num_per_page
      obj_size := lean_size_delta * cur_size

def main : IO Unit := do {
  let rss ← get_rss;
  let pagesize_kB : UInt32 := (←  get_page_size) / (UInt32.ofNat 1024);
  IO.println s!", PAGESIZE: {pagesize_kB}kB";
  IO.println s!"resident size set: {rss}"
  let mut lists : HashMap Nat LinkedList := {};
  for size in [0:max_size_explored] do { -- 524
    IO.print s!"size={size}";
    let t1 : Nat ← IO.monoNanosNow;
    -- size * 8 [length of list]
    let listLen := size * lean_size_delta
    let obj : LinkedList := .mkFromSizeLen listLen n_replicated;
    let t2 : Nat ← IO.monoNanosNow;
    IO.print s!", mk list: {timeDeltaMsString t2 t1}";
    IO.print s!", time per node: {nanosToMillis <| (t2 - t1)/listLen}ms";
    -- keep every 'lean_num_objects_in_page:=1024' objects 
    let obj := obj.keepEvery lean_num_objects_in_page;
    let t3 : Nat ← IO.monoNanosNow;
    IO.print s!", keep every: {timeDeltaMsString t2 t1}";
    lists := lists.insert size obj;
    let t4 : Nat ← IO.monoNanosNow;
    IO.print s!", insertion: {timeDeltaMsString t4 t3}";
    let rss ← get_rss;
    IO.print s!", rss: {rss}#pages";
    let rss_kB := (UInt32.ofNat rss) * pagesize_kB;
    let need_kB := (needUse size)/1024;
    let rss_mB : Float := (Float.ofNat <| rss_kB.toNat) / (Float.ofNat <| 1024);
    let need_mB : Float := (Float.ofNat <| need_kB) / (Float.ofNat <| 1024);
    IO.print s!", memusage: {rss_mB}mB";
    IO.print s!", required: {need_mB}mB";
    IO.print s!", ratio: {need_mB / rss_mB}";
    IO.print ".\n";
  }
  diagonalizePrintLists lists;
}