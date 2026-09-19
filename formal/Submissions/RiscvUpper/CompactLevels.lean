import Submissions.RiscvUpper.CompactChains

/-! Composing the chain phase: the source reads, then fourteen levels of hashes and reads. -/

namespace OptimalOTS.RiscvUpperProgram.Compact

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

def srcs : List Name := (List.finRange 63).map src
def cis (t : Fin 14) : List Name := (List.finRange 63).map fun k => ci k t
def chs (t : Fin 14) : List Name := (List.finRange 63).map fun k => ch k t
def cvs (t : Fin 14) : List Name := (List.finRange 63).map fun k => cv k t
def levelNodes (t : Fin 14) : List Name := cis t ++ chs t ++ cvs t

/-- The tree nodes following every chain node. -/
def treeNodes : List Name :=
  (List.finRange 21).map gc ++ (List.finRange 21).map gh ++ (List.finRange 21).map gv ++
  (List.finRange 7).map ec ++ (List.finRange 7).map eh ++ (List.finRange 7).map ev ++ [rc, rh]

/-- Levels `n` and later, in specification order. -/
def levelsFrom (n : ℕ) : List Name :=
  if h : n < 14 then levelNodes ⟨n, h⟩ ++ levelsFrom (n + 1) else []
termination_by 14 - n

def levelsCodeFrom (n : ℕ) : Code :=
  if h : n < 14 then level n ++ levelsCodeFrom (n + 1) else []
termination_by 14 - n

theorem order_split : order = srcs ++ (levelsFrom 0 ++ treeNodes) := by
  decide +kernel

theorem chains_split :
    (List.finRange 14).flatMap (fun t => level t.val) = levelsCodeFrom 0 := by
  decide +kernel

theorem srcs_nodup : srcs.Nodup :=
  (List.nodup_finRange 63).map fun _ _ h => Name.src.inj h
theorem cis_nodup (t : Fin 14) : (cis t).Nodup :=
  (List.nodup_finRange 63).map fun _ _ h => (Name.ci.inj h).1
theorem chs_nodup (t : Fin 14) : (chs t).Nodup :=
  (List.nodup_finRange 63).map fun _ _ h => (Name.ch.inj h).1
theorem cvs_nodup (t : Fin 14) : (cvs t).Nodup :=
  (List.nodup_finRange 63).map fun _ _ h => (Name.cv.inj h).1

variable (index : Fin (2 ^ 115)) (payload : List Bool) (pk : PublicKey paperParams)

theorem srcs_code (after : List Name) :
    srcs.flatMap (srcSeg index payload pk after).code = readSweep 0 := by
  simp only [srcs, srcSeg, List.flatMap_map, readSweep]
  rfl

theorem cis_code (t : Fin 14) (after : List Name) :
    (cis t).flatMap (ciSeg index payload pk t after).code = [] := by
  simp [cis, ciSeg, List.flatMap_eq_nil_iff]

theorem chs_code (t : Fin 14) (after : List Name) :
    (chs t).flatMap (chSeg index payload pk t after).code = hashSweep t.val := by
  simp only [chs, chSeg, List.flatMap_map, hashSweep]
  rfl

theorem cvs_code (t : Fin 14) (after : List Name) :
    (cvs t).flatMap (cvSeg index payload pk t after).code = readSweep (t.val + 1) := by
  simp only [cvs, cvSeg, List.flatMap_map, readSweep]
  rfl

/-- The cycles charged by the chain segments: read sweeps cost 9 per disclosed chain and 4 per
skipped chain; hash sweeps cost at most 9 per hashed chain and 3 per skipped chain. -/
def srcsCost : ℕ := (srcs.map (srcCost index)).sum
def chsCost (t : Fin 14) : ℕ := ((chs t).map (chCost index t)).sum
def cvsCost (t : Fin 14) : ℕ := ((cvs t).map (cvCost index t)).sum
def levelCost (t : Fin 14) : ℕ := chsCost index t + cvsCost index t

/-- The cycles of levels `n` and later. -/
def levelsCost (n : ℕ) : ℕ := ∑ t : Fin 14, if n ≤ t.val then levelCost index t else 0

theorem levelsCost_lt (n : ℕ) (h : n < 14) :
    levelsCost index n = levelCost index ⟨n, h⟩ + levelsCost index (n + 1) := by
  unfold levelsCost
  have split : ∀ t : Fin 14, (if n ≤ t.val then levelCost index t else 0) =
      (if t = ⟨n, h⟩ then levelCost index t else 0) + (if n + 1 ≤ t.val then levelCost index t else 0) := by
    intro t
    by_cases ht : t = ⟨n, h⟩
    · subst ht
      simp
    · have hne : t.val ≠ n := fun e => ht (Fin.ext e)
      rw [if_neg ht, Nat.zero_add]
      by_cases hle : n ≤ t.val
      · rw [if_pos hle, if_pos (by omega)]
      · rw [if_neg hle, if_neg (by omega)]
  rw [Finset.sum_congr rfl (fun t _ => split t), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem levelsCost_ge (n : ℕ) (h : ¬ n < 14) : levelsCost index n = 0 := by
  unfold levelsCost
  apply Finset.sum_eq_zero
  intro t _
  rw [if_neg (by have := t.isLt; omega)]

/-- A segment charging exactly its code length costs the code's length in total. -/
theorem cost_eq_length (seg : Segment) (nodes : List Name)
    (h : ∀ n ∈ nodes, seg.cost n = (seg.code n).length) :
    (nodes.map seg.cost).sum = (nodes.flatMap seg.code).length := by
  rw [List.length_flatMap]
  congr 1
  exact List.map_congr_left h

theorem srcs_cost (after : List Name) :
    (srcs.map (srcSeg index payload pk after).cost).sum = srcsCost index := rfl

theorem cis_cost (t : Fin 14) (after : List Name) :
    ((cis t).map (ciSeg index payload pk t after).cost).sum = 0 := by
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
  rfl

theorem chs_cost (t : Fin 14) (after : List Name) :
    ((chs t).map (chSeg index payload pk t after).cost).sum = chsCost index t := rfl

theorem cvs_cost (t : Fin 14) (after : List Name) :
    ((cvs t).map (cvSeg index payload pk t after).cost).sum = cvsCost index t := rfl

/-! ## Transitions between segments -/

theorem ci_to_ch (t : Fin 14) (after : List Name) (s : MachineState) (x : graph.Assignment)
    (cursor : ℕ) (h : CiInv index payload pk t (chs t ++ cvs t ++ after) s x cursor []) :
    ChInv index payload pk t (cvs t ++ after) s x cursor (chs t) := by
  obtain ⟨ctx, rep, tagged⟩ := h
  refine ⟨by simpa only [List.nil_append, List.append_assoc] using ctx, ?_⟩
  intro k hk hp
  refine ⟨fun _ => ⟨rep k hk hp, tagged k hk hp (by simp)⟩, fun hn => ?_⟩
  exact absurd (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩) hn

theorem ch_to_cv (t : Fin 14) (after : List Name) (s : MachineState) (x : graph.Assignment)
    (cursor : ℕ) (h : ChInv index payload pk t (cvs t ++ after) s x cursor []) :
    CvInv index payload pk t after s x cursor (cvs t) := by
  obtain ⟨ctx, facts⟩ := h
  refine ⟨by simpa only [List.nil_append] using ctx, ?_⟩
  intro k hk
  have mem : cv k t ∈ cvs t := List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
  exact ⟨fun hp => (facts k hk hp).2 (by simp), fun _ hn => absurd mem hn, fun _ hn => absurd mem hn⟩

theorem src_to_ci (after : List Name) (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (h : SrcInv index payload pk (levelNodes 0 ++ after) s x cursor []) :
    CiInv index payload pk 0 (chs 0 ++ cvs 0 ++ after) s x cursor (cis 0) := by
  obtain ⟨ctx, holds⟩ := h
  refine ⟨by simpa only [List.nil_append, levelNodes, List.append_assoc] using ctx, ?_, ?_⟩
  · intro k hk hp
    have hp0 : pos index k = 0 := by
      change (fixedPositions index k).val ≤ 0 at hp
      show (fixedPositions index k).val = 0
      omega
    have prevEq : prev k 0 = src k := by unfold prev; simp
    rw [prevEq]
    exact holds k hk hp0 (by simp)
  · intro k _ _ hn
    exact absurd (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩) hn

theorem prev_succ (k : Fin 63) (t : Fin 14) (ht : t.val + 1 < 14) :
    prev k ⟨t.val + 1, ht⟩ = cv k t := by
  unfold prev
  rw [dif_neg (by simp)]
  all_goals (try (congr 1; try (ext; simp)))

/-- The chain values of level `t` are the inputs of level `t + 1`. -/
theorem cv_to_ci (t : Fin 14) (ht : t.val + 1 < 14) (after : List Name) (s : MachineState)
    (x : graph.Assignment) (cursor : ℕ)
    (h : CvInv index payload pk t (levelNodes ⟨t.val + 1, ht⟩ ++ after) s x cursor []) :
    CiInv index payload pk ⟨t.val + 1, ht⟩ (chs ⟨t.val + 1, ht⟩ ++ cvs ⟨t.val + 1, ht⟩ ++ after)
      s x cursor (cis ⟨t.val + 1, ht⟩) := by
  obtain ⟨ctx, facts⟩ := h
  refine ⟨by simpa only [List.nil_append, levelNodes, List.append_assoc] using ctx, ?_, ?_⟩
  · intro k hk hp
    rw [prev_succ k t ht]
    obtain ⟨h1, h2, h3⟩ := facts k hk
    change (fixedPositions index k).val ≤ t.val + 1 at hp
    rcases Nat.lt_or_ge (fixedPositions index k).val (t.val + 1) with lt | ge
    · have hp' : pos index k ≤ t.val := by show (fixedPositions index k).val ≤ t.val; omega
      rw [h2 hp' (by simp)]
      unfold Holds
      apply (Direct.memBits_cast _ _ _ _).mpr
      exact (h1 hp').trunc
    · exact h3 (by show (fixedPositions index k).val = t.val + 1; omega) (by simp)
  · intro k _ _ hn
    exact absurd (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩) hn

/-- After the last level every active chain holds its final value. -/
def ChainsDone (s : MachineState) (x : graph.Assignment) (cursor : ℕ) : Prop :=
  ChainCtx index payload pk s cursor treeNodes ∧
  ∀ k : Fin 63, k.val < 36 → Holds s k (x (cv k 13).fin)

theorem cv_last (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (h : CvInv index payload pk 13 treeNodes s x cursor []) :
    ChainsDone index payload pk s x cursor := by
  obtain ⟨ctx, facts⟩ := h
  refine ⟨by simpa only [List.nil_append] using ctx, ?_⟩
  intro k hk
  obtain ⟨h1, h2, h3⟩ := facts k hk
  have bound := (fixedPositions index k).isLt
  rcases Nat.lt_or_ge (fixedPositions index k).val 14 with lt | ge
  · have hp' : pos index k ≤ 13 := by show (fixedPositions index k).val ≤ 13; omega
    rw [h2 hp' (by simp)]
    unfold Holds
    apply (Direct.memBits_cast _ _ _ _).mpr
    exact (h1 hp').trunc
  · exact h3 (by show (fixedPositions index k).val = 13 + 1; omega) (by simp)

/-! ## One level -/

theorem level_refines (t : Fin 14) (after : List Name) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp (Spec paperParams) (Option Bool)) (c rest' : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment) (cursor' : ℕ),
      CvInv index payload pk t after u y cursor' [] → Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, cursor')) c) :
    ∀ (s : MachineState) (x : graph.Assignment) (cursor fuel : ℕ),
      CiInv index payload pk t (chs t ++ cvs t ++ after) s x cursor (cis t) →
      Riscv.CodeAt s s.pc (level t.val ++ tail) → (level t.val).length + rest' ≤ fuel →
      Riscv.Refines fuel s (runNodes' index payload (levelNodes t) x cursor >>= K)
        (levelCost index t + c) := by
  intro s x cursor fuel inv located bound
  have hashLen : (level t.val).length = (hashSweep t.val).length + (readSweep (t.val + 1)).length := by
    simp [level]
  simp only [levelNodes, runNodes'_append, bind_assoc]
  have step1 := sweep_refines index payload (ciSeg index payload pk t (chs t ++ cvs t ++ after)) (cis t)
    (cis_nodup t) (fun n hn => by
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hn
      exact ci_refines index payload pk t (chs t ++ cvs t ++ after) k) (level t.val ++ tail)
    (fun r => runNodes' index payload (chs t) r.1 r.2 >>= fun r' =>
      runNodes' index payload (cvs t) r'.1 r'.2 >>= K)
    (levelCost index t + c) ((level t.val).length + rest') ?_ s x cursor fuel inv
    (by rw [cis_code]; exact located) (by rw [cis_code]; simpa using bound)
  · rw [cis_cost, Nat.zero_add] at step1
    exact step1
  intro u y cursor' inv1 located1 left hleft
  dsimp only
  have step2 := sweep_refines index payload (chSeg index payload pk t (cvs t ++ after)) (chs t)
    (chs_nodup t) (fun n hn => by
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hn
      exact ch_refines index payload pk t (cvs t ++ after) k) (readSweep (t.val + 1) ++ tail)
    (fun r' => runNodes' index payload (cvs t) r'.1 r'.2 >>= K)
    (cvsCost index t + c) ((readSweep (t.val + 1)).length + rest') ?_ u y cursor' left
    (ci_to_ch index payload pk t after u y cursor' inv1)
    (by rw [chs_code]; simpa only [level, List.append_assoc] using located1)
    (by rw [chs_code]; omega)
  · rw [chs_cost] at step2
    rw [levelCost, Nat.add_assoc]
    exact step2
  intro v z cursor'' inv2 located2 left' hleft'
  dsimp only
  have step3 := sweep_refines index payload (cvSeg index payload pk t after) (cvs t) (cvs_nodup t)
    (fun n hn => by
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hn
      exact cv_refines index payload pk t after k) tail K c rest' continuation v z cursor'' left'
    (ch_to_cv index payload pk t after v z cursor'' inv2)
    (by rw [cvs_code]; exact located2) (by rw [cvs_code]; exact hleft')
  rw [cvs_cost] at step3
  exact step3


/-! ## All levels -/

theorem levelsFrom_lt (n : ℕ) (h : n < 14) :
    levelsFrom n = levelNodes ⟨n, h⟩ ++ levelsFrom (n + 1) := by
  rw [levelsFrom, dif_pos h]

theorem levelsFrom_ge (n : ℕ) (h : ¬ n < 14) : levelsFrom n = [] := by
  rw [levelsFrom, dif_neg h]

theorem levelsCodeFrom_lt (n : ℕ) (h : n < 14) :
    levelsCodeFrom n = level n ++ levelsCodeFrom (n + 1) := by
  rw [levelsCodeFrom, dif_pos h]

theorem levelsCodeFrom_ge (n : ℕ) (h : ¬ n < 14) : levelsCodeFrom n = [] := by
  rw [levelsCodeFrom, dif_neg h]

/-- The machine state at the start of level `n`, or after the last level. -/
def LevelStart (n : ℕ) (s : MachineState) (x : graph.Assignment) (cursor : ℕ) : Prop :=
  if h : n < 14 then
    CiInv index payload pk ⟨n, h⟩ (chs ⟨n, h⟩ ++ cvs ⟨n, h⟩ ++ (levelsFrom (n + 1) ++ treeNodes))
      s x cursor (cis ⟨n, h⟩)
  else ChainsDone index payload pk s x cursor

theorem levels_refines (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp (Spec paperParams) (Option Bool)) (c rest' : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment) (cursor' : ℕ),
      ChainsDone index payload pk u y cursor' → Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, cursor')) c) :
    ∀ (m n : ℕ), 14 - n = m → ∀ (s : MachineState) (x : graph.Assignment) (cursor fuel : ℕ),
      LevelStart index payload pk n s x cursor →
      Riscv.CodeAt s s.pc (levelsCodeFrom n ++ tail) → (levelsCodeFrom n).length + rest' ≤ fuel →
      Riscv.Refines fuel s (runNodes' index payload (levelsFrom n) x cursor >>= K)
        (levelsCost index n + c) := by
  intro m
  induction m with
  | zero =>
    intro n hn s x cursor fuel start located bound
    have h : ¬ n < 14 := by omega
    rw [levelsFrom_ge n h, levelsCost_ge index n h]
    rw [levelsCodeFrom_ge n h] at located bound
    unfold LevelStart at start
    rw [dif_neg h] at start
    simp only [runNodes', pure_bind, List.length_nil, Nat.zero_add]
    simp only [List.nil_append, List.length_nil, Nat.zero_add] at located bound
    exact continuation s x cursor start located fuel bound
  | succ m ih =>
    intro n hn s x cursor fuel start located bound
    have h : n < 14 := by omega
    rw [levelsFrom_lt n h, levelsCost_lt index n h]
    rw [levelsCodeFrom_lt n h] at located bound
    unfold LevelStart at start
    rw [dif_pos h] at start
    rw [runNodes'_append, bind_assoc, Nat.add_assoc]
    rw [List.append_assoc] at located
    rw [List.length_append] at bound
    apply level_refines index payload pk ⟨n, h⟩ (levelsFrom (n + 1) ++ treeNodes)
      (levelsCodeFrom (n + 1) ++ tail)
      (fun r => runNodes' index payload (levelsFrom (n + 1)) r.1 r.2 >>= K)
      (levelsCost index (n + 1) + c) ((levelsCodeFrom (n + 1)).length + rest') ?_
      s x cursor fuel start located
      (by show (level n).length + ((levelsCodeFrom (n + 1)).length + rest') ≤ fuel; omega)
    intro u y cursor' inv located' left hleft
    dsimp only
    apply ih (n + 1) (by omega) u y cursor' left ?_ located' hleft
    unfold LevelStart
    split_ifs with h'
    · rw [levelsFrom_lt (n + 1) h', List.append_assoc] at inv
      exact cv_to_ci index payload pk ⟨n, h⟩ h' (levelsFrom (n + 1 + 1) ++ treeNodes) u y cursor' inv
    · have h13 : n = 13 := by omega
      subst h13
      rw [levelsFrom_ge 14 (by decide), List.nil_append,
        show (⟨13, h⟩ : Fin 14) = 13 from rfl] at inv
      exact cv_last index payload pk u y cursor' inv

/-! ## The whole chain phase -/

theorem chainSetup_effect (s : MachineState) :
    (chainSetup.foldl execInstrBr s).getReg .x18 = BitVec.ofNat 64 chainsBase ∧
    (chainSetup.foldl execInstrBr s).getReg .x9 = Riscv.signatureBase + 32 + BitVec.ofNat 64 (0 / 8) ∧
    (chainSetup.foldl execInstrBr s).getReg .x5 = Riscv.hashCall ∧
    (chainSetup.foldl execInstrBr s).getReg .x11 = 144 ∧
    (∀ r, r ≠ .x18 → r ≠ .x9 → r ≠ .x5 → r ≠ .x11 →
      (chainSetup.foldl execInstrBr s).getReg r = s.getReg r) ∧
    (chainSetup.foldl execInstrBr s).mem = s.mem := by
  have baseLit : literalValue chainsBase = BitVec.ofNat 64 chainsBase := by decide +kernel
  have cursorLit : literalValue (Riscv.signatureBase.toNat + 32) =
      Riscv.signatureBase + 32 + BitVec.ofNat 64 (0 / 8) := by decide +kernel
  simp only [chainSetup, List.foldl_append, List.foldl_cons, List.foldl_nil, execInstrBr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x11 .x18 _ (by decide),
      MachineState.getReg_setReg_ne _ .x5 .x18 _ (by decide),
      constant_preserves _ .x9 .x18 _ (by decide), constant_value _ .x18 _ (by decide), baseLit]
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x11 .x9 _ (by decide),
      MachineState.getReg_setReg_ne _ .x5 .x9 _ (by decide),
      constant_value _ .x9 _ (by decide), cursorLit]
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x11 .x5 _ (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x5 ≠ .x0), getReg_x0]
    try rfl
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x11 ≠ .x0),
      getReg_x0]
    try rfl
  · intro r h18 h9 h5 h11
    simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x11 r _ h11.symm,
      MachineState.getReg_setReg_ne _ .x5 r _ h5.symm, constant_preserves _ .x9 r _ h9.symm,
      constant_preserves _ .x18 r _ h18.symm]
  · simp only [MachineState.setPC, MachineState.setReg, constant_mem]
    try rfl

theorem chainSetup_ready (s : MachineState) : Riscv.LinearReady s chainSetup := by
  refine ((constant_ready _ _ _).append (constant_ready _ _ _)).append ?_
  exact ⟨rfl, trivial, rfl, trivial, trivial⟩

theorem chainSetup_length : chainSetup.length = 6 := by decide +kernel

/-- Entering the chain phase from the decoded input establishes the source invariant. -/
theorem chainSetup_srcInv (s : MachineState) (context : Direct.ExecutionContext s index payload pk)
    (x : graph.Assignment) :
    SrcInv index payload pk (levelsFrom 0 ++ treeNodes) (chainSetup.foldl execInstrBr s) x 0 srcs := by
  obtain ⟨h18, h9, h5, h11, regs, mem⟩ := chainSetup_effect s
  refine ⟨⟨context.frameInputs (fun addr _ => by simp only [MachineState.getMem, mem])
    (regs .x8 (by decide) (by decide) (by decide) (by decide)), ⟨h18, h5, h11⟩, h9, rfl, ?_⟩, ?_⟩
  · rw [← order_split, total_consumed]
  · intro k _ _ hn
    exact absurd (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩) hn

theorem srcs_length_code : (readSweep 0).length = ((List.finRange 63).flatMap
    fun k => if k.val < 36 then readChain 0 k.val else []).length := rfl

/-- The cycles of the whole chain phase for a given index. -/
def chainsCost : ℕ := chainSetup.length + (srcsCost index + levelsCost index 0)

/-- The whole chain phase refines the reader over the chain nodes of `order`. -/
theorem chains_refines (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp (Spec paperParams) (Option Bool)) (c rest' : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment) (cursor' : ℕ),
      ChainsDone index payload pk u y cursor' → Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, cursor')) c)
    (s : MachineState) (context : Direct.ExecutionContext s index payload pk)
    (x : graph.Assignment) (fuel : ℕ)
    (located : Riscv.CodeAt s s.pc (chains ++ tail)) (bound : chains.length + rest' ≤ fuel) :
    Riscv.Refines fuel s (runNodes' index payload (srcs ++ levelsFrom 0) x 0 >>= K)
      (chainsCost index + c) := by
  have parts : chains = chainSetup ++ (readSweep 0 ++ (levelsCodeFrom 0 ++ [])) := by
    simp only [chains, chains_split, List.append_nil, List.append_assoc]
  rw [parts] at located bound
  simp only [List.append_assoc, List.length_append, List.length_nil, Nat.add_zero] at located bound
  set u := chainSetup.foldl execInstrBr s with hu
  have ready := chainSetup_ready s
  have uCode : Riscv.CodeAt u u.pc (readSweep 0 ++ (levelsCodeFrom 0 ++ tail)) := by
    rw [hu, Riscv.linear_fold_pc s _ ready]
    exact located.append_right.code_eq (Riscv.fold_code s _)
  have inv := chainSetup_srcInv index payload pk s context x
  rw [runNodes'_append, bind_assoc]
  rw [show fuel = chainSetup.length + (fuel - chainSetup.length) by rw [chainSetup_length] at bound ⊢; omega,
    show chainsCost index + c = chainSetup.length + (srcsCost index + (levelsCost index 0 + c)) by
      unfold chainsCost; omega]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hu]
  have step := sweep_refines index payload (srcSeg index payload pk (levelsFrom 0 ++ treeNodes)) srcs
    srcs_nodup (fun n hn => by
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hn
      exact src_refines index payload pk (levelsFrom 0 ++ treeNodes) k) (levelsCodeFrom 0 ++ tail)
    (fun r => runNodes' index payload (levelsFrom 0) r.1 r.2 >>= K)
    (levelsCost index 0 + c) ((levelsCodeFrom 0).length + rest') ?_ u x 0
    (fuel - chainSetup.length) inv (by rw [srcs_code]; exact uCode)
    (by rw [srcs_code, chainSetup_length] at *; omega)
  · rw [srcs_cost] at step
    exact step
  intro v y cursor' inv' located' left hleft
  dsimp only
  apply levels_refines index payload pk tail K c rest' continuation 14 0 rfl v y cursor' left ?_
    located' hleft
  unfold LevelStart
  rw [dif_pos (by decide)]
  exact src_to_ci index payload pk (levelsFrom 1 ++ treeNodes) v y cursor'
    (by rwa [levelsFrom_lt 0 (by decide), List.append_assoc] at inv')

end OptimalOTS.RiscvUpperProgram.Compact
