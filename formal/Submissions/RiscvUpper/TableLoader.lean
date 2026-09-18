import Submissions.RiscvUpper.IndexInput
import Submissions.RiscvUpper.DecoderArithmetic
import Submissions.RiscvUpper.HashOutput

/-! The immutable composition-count table is loaded at its exact decoder addresses. -/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

/-- Slicing a fixed-width flat map selects the corresponding slice of one entry. -/
theorem flatMap_slice {α β : Type} (xs : List α) (f : α → List β) (width : ℕ)
    (uniform : ∀ a ∈ xs, (f a).length = width)
    (j k len : ℕ) (hj : j < xs.length) (contained : k + len ≤ width) :
    ((xs.flatMap f).drop (width * j + k)).take len = ((f xs[j]).drop k).take len := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons a xs ih =>
    have ha := uniform a (by simp)
    cases j with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero, List.flatMap_cons]
      rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by
        simp only [List.length_drop, ha]; omega)]
    | succ j =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.drop_append, List.drop_eq_nil_iff.mpr (by rw [ha, Nat.mul_succ]; omega : (f a).length ≤ width * (j + 1) + k)]
      simp only [List.nil_append, ha]
      have hoff : width * (j + 1) + k - width = width * j + k := by rw [Nat.mul_succ]; omega
      rw [hoff]
      exact ih (fun a h => uniform a (by simp [h])) j (by simpa using hj)

private theorem compositionTable_size (n : ℕ) : (Forest.compositionTable 121 n).length = 122 := by
  cases n <;> simp [Forest.compositionTable]

private theorem tableRow_length (n : ℕ) :
    ((Forest.compositionTable 121 n).flatMap fun count =>
      Riscv.bytesOfVector (BitVec.ofNat 128 count)).length = 1952 := by
  simp [List.length_flatMap, compositionTable_size]

/-- Each table doubleword is the corresponding half of its encoded composition count. -/
theorem tableData_word (n sum j : ℕ) (hn : n < 36) (hs : sum ≤ 121) (hj : j < 2) :
    bytesToWordLE ((tableData.drop (8 * (2 * (122 * n + sum) + j))).take 8) =
      (BitVec.ofNat 128 (Forest.comp n sum)).extractLsb' (64 * j) 64 := by
  have hoff : 8 * (2 * (122 * n + sum) + j) = 1952 * n + (16 * sum + 8 * j) := by omega
  rw [hoff, tableData, flatMap_slice _ _ 1952 (fun n _ => tableRow_length n)
    n (16 * sum + 8 * j) 8 (by simpa using hn) (by omega)]
  simp only [List.getElem_range]
  rw [flatMap_slice _ _ 16 (by intros; simp) sum (8 * j) 8
    (by rw [compositionTable_size]; omega) (by omega)]
  have hcount : (Forest.compositionTable 121 n)[sum]'(by rw [compositionTable_size]; omega) =
      Forest.comp n sum := by
    have h := Forest.compositionTable_get 121 n sum hs
    have hi : sum < (Forest.compositionTable 121 n).length := by rw [compositionTable_size]; omega
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using h
  rw [hcount, bytesToWordLE_bytesOfVector]

theorem initialState_table_word (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (hdata : image.data = tableData)
    (n sum j : ℕ) (hn : n < 36) (hs : sum ≤ 121) (hj : j < 2) :
    (Riscv.initialState image pk m bits).getMem
      (tableAddress n sum + BitVec.ofNat 64 (8 * j)) =
      (BitVec.ofNat 128 (Forest.comp n sum)).extractLsb' (64 * j) 64 := by
  have haddr : tableAddress n sum + BitVec.ofNat 64 (8 * j) =
      Riscv.dataBase + BitVec.ofNat 64 (8 * (2 * (122 * n + sum) + j)) := by
    rw [tableAddress, ← BitVec.ofNat_add]
    change _ = BitVec.ofNat 64 Riscv.dataBase.toNat + _
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  rw [haddr, initialState_getMem, getMem_load_outside, loaderMessage,
    getMem_load_outside, loaderPublic, getMem_load_outside, loaderData, hdata,
    getMem_writeBytesAsWords, tableData_word n sum j hn hs hj]
  all_goals norm_num [tableData_length, Riscv.bytesOfVector, Riscv.bytesOfBits, paperParams,
    BitVec.toNat_add] <;> omega

/-- The initial ABI installs every composition count at the decoder's prescribed address. -/
theorem initialState_table (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (hdata : image.data = tableData) :
    TableLoaded (Riscv.initialState image pk m bits) := by
  intro n hn sum hs
  have hlo := initialState_table_word image pk m bits hdata n sum 0 hn hs (by decide)
  have hhi := initialState_table_word image pk m bits hdata n sum 1 hn hs (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, BitVec.add_zero] at hlo hhi
  rw [joinWords, hlo, show (8 : Word) = BitVec.ofNat 64 8 from rfl, hhi]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  by_cases hilow : i < 64
  · simp [hilow]
  · have hisub : i - 64 < 64 := by omega
    simp [hilow, hisub, show 64 + (i - 64) = i by omega]

theorem tableAddress_toNat (n sum : ℕ) (hn : n < 36) (hs : sum ≤ 121) :
    (tableAddress n sum).toNat = 2097152 + 1952 * n + 16 * sum := by
  unfold tableAddress
  rw [BitVec.toNat_ofNat, dataBase_toNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Preparing the index query preserves the immutable decoder table. -/
theorem indexInput_table (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (hdata : image.data = tableData) :
    TableLoaded (indexInputState image pk m bits) := by
  intro n hn sum hs
  rw [indexInput_frame_interval, indexInput_frame_interval]
  · exact initialState_table image pk m bits hdata n hn sum hs
  all_goals
    left
    simp only [BitVec.toNat_add, tableAddress_toNat n sum hn hs,
      show (8 : Word).toNat = 8 from rfl]
    try rw [Nat.mod_eq_of_lt (by omega)]
    unfold scratchBase
    omega

/-- The first HASH output is disjoint from every immutable table word. -/
theorem indexHash_table (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (hdata : image.data = tableData)
    (answer : BitVec 256) :
    TableLoaded (Riscv.writeHash (indexInputState image pk m bits) answer) := by
  intro n hn sum hs
  rw [writeHash_frame, writeHash_frame]
  · exact indexInput_table image pk m bits hdata n hn sum hs
  all_goals
    intro j hj heq
    have hr := (indexInput_registers image pk m bits).2.2.2.1
    rw [hr] at heq
    have h := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_add, tableAddress_toNat n sum hn hs, BitVec.toNat_ofNat,
      show (8 : Word).toNat = 8 from rfl] at h
    have htable : 2097152 + 1952 * n + 16 * sum + 8 < 2 ^ 64 := by omega
    have hout : scratchBase + 128 + 8 * j < 2 ^ 64 := by unfold scratchBase; omega
    have hj8 : 8 * j < 2 ^ 64 := by omega
    norm_num only [scratchBase, Nat.reduceAdd, Nat.reducePow] at h hout htable hj8
    rw [Nat.mod_eq_of_lt hj8] at h
    try rw [Nat.mod_eq_of_lt htable] at h
    rw [Nat.mod_eq_of_lt hout] at h
    omega

end OptimalOTS.RiscvUpperProgram
