import Lean
open Lean

#check UInt64

/-- type that is 8(n + 1) bytes long. -/
@[reducible, simp]
def Data : Nat → Type
| 0 => UInt64
| n + 1 => UInt64 × Data n

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

/-- make arrays that replicate an object size 'σ' 'len' times, and smoosh them into a linked list. -/
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

def LinkedList.length : LinkedList → Nat
| .Nil => 0
| .Cons _ xs => 1 + xs.length

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

def lean_num_objects_in_page : Nat := lean_page_size / lean_size_delta -- 1024
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

/-
static inline size_t lean_align(size_t v, size_t a) {
    return (v / a)*a + a * (v % a != 0);
}
-/

/-- align 'v' to alignment 'a'. -/
def align (v : Nat) (a : Nat) : Nat :=
  (v / a) * a + (if v % a == 0 then 0 else a)

/-- ceil divide. -/
def ceilDiv (p q : Nat) :=
  (p + q - 1) / q

/-- floor divide. -/
def floorDiv (p q : Nat) := p / q

-- # of bytes we are retaining.
-- Off by the boxing/pointers
def needUseBytes (cur_size : Nat) : Nat :=
match cur_size with
 | 0 => 0
 | .succ cur_size' =>
    obj_size*num_kept + needUseBytes cur_size' where
      num_per_page := (lean_page_size/obj_size)
      num_kept := n_replicated/num_per_page
      obj_size := align cur_size lean_size_delta

-- Step 1: Allocate 9 and check how much space it takes
-- Step 2: Allocate 9000 and check how much space that takes
-- Step 3: drop every 1024 and check how much space that takes.

def rss_mB : IO Float := do
  let rss_num_pages ← get_rss;
  -- IO.print s!", rss: {rss_num_pages}#pages";
  let pagesize_kB : UInt32 := (←  get_page_size) / (UInt32.ofNat 1024);
  let rss_kB := (UInt32.ofNat rss_num_pages) * pagesize_kB;
  let rss_mB : Float := (Float.ofNat <| rss_kB.toNat) / (Float.ofNat <| 1024);
  return rss_mB

def simpleMain : IO Unit := do {
  let rss_num_pages ← get_rss;
  let pagesize_kB : UInt32 := (←  get_page_size) / (UInt32.ofNat 1024);
  IO.println s!", PAGESIZE: {pagesize_kB}kB";
  IO.println s!"resident size set (#pages): {rss_num_pages}";
  for size in [0:max_size_explored] do { -- 524
    let objectAllocSize : Nat := size * lean_size_delta;
    let smallListLen : Nat := ceilDiv n_replicated lean_num_objects_in_page;
    IO.print s!"objectAllocSize={objectAllocSize} | ";
    let rss_start ← rss_mB;
    let rss_cur := rss_start;
    IO.print s!"rss(start): {rss_start}mB | ";

    /- make a large object. -/
    let largeObj : LinkedList := .mkFromSizeLen objectAllocSize n_replicated;
    let rss_largeObj ← rss_mB;
    let largeObjLen := largeObj.length
    let delta : Float := rss_largeObj - rss_cur;
    let rss_cur := rss_largeObj;
    IO.print s!"largeObj length:{largeObjLen}, rss:{rss_largeObj}mB, Δ({delta}mB) | ";

    /- drop data from the large object -/
    let droppedLargeObj : LinkedList := largeObj.keepEvery lean_num_objects_in_page;
    let rss_droppedLargeObj ← rss_mB;
    let droppedLrgeObjLen := droppedLargeObj.length
    let delta : Float := rss_droppedLargeObj - rss_cur;
    let rss_cur := rss_largeObj;
    IO.print s!"droppedLrgeObjLen length:{droppedLrgeObjLen}, rss:{rss_droppedLargeObj}mB, Δ({delta}mB) | ";

    /- make a small object. -/
    let smallObj : LinkedList := .mkFromSizeLen objectAllocSize smallListLen;
    let rss_smallObj ← rss_mB;
    let smallObjLen := smallObj.length /- smallObj should be dropped here! But is it? -/
    let delta : Float := rss_smallObj - rss_cur;
    let rss_cur := rss_smallObj;
    IO.print s!"smallObj length:{smallObjLen}, rss:{rss_smallObj}mB, Δ({delta}mB) | ";

    /- newline -/
    IO.print ".\n";

  }
   return ();
}


def adverserialMain : IO Unit := do {
  let rss_num_pages ← get_rss;
  let pagesize_kB : UInt32 := (←  get_page_size) / (UInt32.ofNat 1024);
  IO.println s!", PAGESIZE: {pagesize_kB}kB";
  IO.println s!"resident size set (#pages): {rss_num_pages}"
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
    let origLen := obj.length
    let obj := obj.keepEvery lean_num_objects_in_page;
    let finalLen : Nat := LinkedList.length obj;
    IO.print s!", length original({origLen})/final({finalLen})";
    let t3 : Nat ← IO.monoNanosNow;
    IO.print s!", keep every: {timeDeltaMsString t2 t1}";
    lists := lists.insert size obj;
    let t4 : Nat ← IO.monoNanosNow;
    IO.print s!", insertion: {timeDeltaMsString t4 t3}";
    let rss_num_pages ← get_rss;
    IO.print s!", rss: {rss_num_pages}#pages";
    let rss_kB := (UInt32.ofNat rss_num_pages) * pagesize_kB;
    let need_kB := (needUseBytes size)/1024;
    let rss_mB : Float := (Float.ofNat <| rss_kB.toNat) / (Float.ofNat <| 1024);
    let need_mB : Float := (Float.ofNat <| need_kB) / (Float.ofNat <| 1024);
    IO.print s!", memusage: {rss_mB}mB";
    IO.print s!", required: {need_mB}mB";
    IO.print s!", ratio: {need_mB / rss_mB}";
    IO.print ".\n";
  }
  diagonalizePrintLists lists;
}

def main : IO Unit := simpleMain
