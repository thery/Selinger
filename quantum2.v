From HB Require Import structures.
Require Import s2int quantum.

Set Implicit Arguments.
Unset Strict Implicit.
From mathcomp Require Import all_ssreflect all_algebra all_field.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory zmodp.

Import perm fingroup.
Open Scope ring_scope.
Open Scope S2I_scope.

Section OSK.

Variable n k : nat.
Record OSK : predArgType := OSKof {
  OSKm :> 'M[algC]_n;
  OSKos : OSKm \is k.-unitary }.

Lemma OSKs (M : OSK) : OSKm M \is k.-sunitary.
Proof. by exact: mxounitary_sunitary (OSKos M). Qed.
 
Lemma OSKo (M : OSK) : OSKm M \is k.-odd.
Proof. by case/and3P : (OSKos M). Qed.

HB.instance Definition _ := [isSub for OSKm].
HB.instance Definition _ := [Countable of OSK by <:].

End OSK.
 
Section M.

Definition bdiag_mx n (bs : {ffun 'I_n -> bool}) : 'M[algC]_n := 
  diag_mx (\row_(i < n) (-1) ^+ (bs i)).

Lemma bdiagM n (bs1 bs2  : {ffun 'I_n -> bool}) :
  bdiag_mx [ffun i => (bs1 i) (+) (bs2 i)] =
   (bdiag_mx bs1) *m bdiag_mx bs2.
Proof.
apply/matrixP=> i j; rewrite !(mxE, ffunE).
have [/eqP<-|iDj] := boolP (i == j).
  rewrite (bigD1 i) //= big1 => [|i1 H].
    by rewrite !mxE eqxx !mulr1n addr0 signr_addb.
  by rewrite !mxE eq_sym !(negPf H) !mulr0n mulr0.
rewrite mulr0n big1 // => i1 _; rewrite !mxE.
have [/eqP<-|iDi1] := boolP (i == i1); last first.
  by rewrite mulr0n mul0r.
by rewrite (negPf iDj) mulr0n mulr0.
Qed.

Lemma bdiag_perm_mx n (bs : {ffun 'I_n -> bool}) (s : 'S_n) :
  bdiag_mx [ffun i => bs (s i)] *m perm_mx s = perm_mx s *m bdiag_mx bs.
Proof.
apply/matrixP=> i j; rewrite !(mxE, ffunE).
rewrite (bigD1 ((invg s) j)) //=.
rewrite big1 => [|i1]; rewrite ?mulr0; last first.
  rewrite !(mxE, ffunE) -(inj_eq (@perm_inj _ s)) -permM.
  rewrite mulVg permE => /negPf->.
  by rewrite mulr0n mulr0.
rewrite addr0  (bigD1 (s i)) //=.
rewrite big1 => [|i1]; rewrite ?mulr0; last first.
  by rewrite eq_sym !mxE => /negPf->; rewrite mul0r.
rewrite addr0 !(mxE, ffunE) -permM mulVg /= perm1 !eqxx mulr1n.
by rewrite -(inj_eq (@perm_inj _ s)) -permM mulVg perm1 mul1r mulr1.
Qed.

Definition mcol_nz n (R : ringType) (M : 'M[R]_n) :=
  [ffun i =>  odflt i [pick j | M i j != 0]].

Lemma mcol_nz_nz n (M : 'M_n) i : M \is mxunitary -> M i (mcol_nz M i) != 0.
Proof.
rewrite ffunE; case: pickP => // H.
move=> /mxunitaryP /(_ i i)/eqP.
rewrite eqxx big1 => [|i1 _].
  by rewrite eq_sym (negPf (oner_neq0 _)).
by have /eqP-> := H i1; rewrite mul0r.
Qed.

Lemma mcol_nz_eq1 n (M : 'M_n) i : 
  M \is 0.-sunitary ->  (M i (mcol_nz M i) == 1) || (M i (mcol_nz M i) == -1).
Proof.
move=> Hs2.
set j := mcol_nz _ _.
have F i1 j1  : M i1 j1 \is a s2Int.
  by have := mxsunitary_s2int i1 j1 Hs2; rewrite mul1r.
have F1 : \sum_(k < n) (M i k) ^+ 2 = 1.
  have /andP[/mxunitaryP/(_ i i)] := Hs2.
  rewrite eqxx mulr1n /= => <- _.
  apply: eq_bigr => k _.
  by rewrite expr2 conj_Creal // Creal_s2Int.
have := congr1 s2intA F1.
rewrite (s2intA_nat 1) /= s2intA_sum /= => [|k _ _]; last first.
  by rewrite expr2 rpredM.
rewrite (bigD1 j) //= => H1.
suff /s2intA_sqrt_eq1 : s2intA (M i j ^+ 2) = 1 => [/(_ (F _ _))|].
  by rewrite orbC.
apply: le_anti.
rewrite -{1}[1]H1 lerDl s2intA_sqrt_gt1 ?andbT //; last first.
  by apply: mcol_nz_nz; case/andP: Hs2.
elim/big_rec: _ => // k y _ yP.
apply: addr_ge0 => //.
have [/eqP->|nZxs] := boolP (M i k == 0).
  by rewrite expr0n (s2intA_nat 0).
by apply: le_trans (s2intA_sqrt_gt1  _ _).
Qed.

Lemma mcol_nz_eq0 n (M : 'M_n) i j :
  M \is 0.-sunitary -> j != mcol_nz M i -> M i j = 0.
Proof.
move=> Hs2 jDncol.
have F i1 j1  : M i1 j1 \is a s2Int.
  by have := mxsunitary_s2int i1 j1 Hs2; rewrite mul1r.
have F1 : \sum_(k < n) (M i k) ^+ 2 = 1.
  have /andP[/mxunitaryP/(_ i i)] := Hs2.
  rewrite eqxx mulr1n /= => <- _.
  apply: eq_bigr => k _.
  by rewrite expr2 conj_Creal // Creal_s2Int.
have := congr1 s2intA F1.
rewrite (s2intA_nat 1) /= s2intA_sum /= => [|k _ _]; last first.
  by rewrite expr2 rpredM.
have [/eqP-> //|nE] := boolP (M i j == 0).
rewrite (bigD1 (mcol_nz M i)) //= (_ : _ ^+2 = 1); last first.
  by have /orP[/eqP->|/eqP->] := (mcol_nz_eq1 i Hs2); rewrite ?sqrrN expr1n.
move/eqP; rewrite (s2intA_nat 1) eq_sym addrC -subr_eq eq_sym subrr.
rewrite psumr_eq0=> [/allP|j1 Hj1]; last first.
  have [/eqP->|/(s2intA_sqrt_gt1 (F _ _))] := boolP (M i j1 == 0).
    by by rewrite expr0n s2intA_nat.
  by move/(le_trans _)->.
move=> /(_ j (mem_index_enum _)); rewrite jDncol /= => /eqP H1.
by have := s2intA_sqrt_gt1 (F _ _) nE; rewrite H1.
Qed.

Lemma mcol_nz_inj n (M : 'M_n) : M \is 0.-sunitary -> injective (mcol_nz M).
Proof.
move=> Hs2 i j Hij.
have /andP[Hs1 _] := Hs2.
have /mxunitaryP/(_ i j) := Hs1.
case: eqP => // iDj.
rewrite mulr0n  (bigD1 (mcol_nz M i)) //= big1 => [|i1 Hi1]; last first.
  by rewrite mcol_nz_eq0 // mul0r.
rewrite addr0 {2}Hij => /eqP.
by rewrite mulf_eq0 conjC_eq0 !(negPf (mcol_nz_nz _ _)).
Qed.

Lemma mxsunitary_perm_mx n (p : 'S_n) : perm_mx p \is 0.-sunitary.
Proof.
apply/andP; split; last first.
  by apply/forallP => i; apply/forallP=> j; rewrite !mxE ?mul1r // rpred_nat.
apply/mxunitaryP=> i j.
rewrite (bigD1 (p i)) //= !mxE !eqxx !mul1r (inj_eq (@perm_inj _ _)) //.
rewrite eq_sym big1 ?addr0 ?conjC_nat => // i1 Hi1.
by rewrite !mxE eq_sym (negPf Hi1) mul0r.
Qed.

Lemma mxsunitary_bdiag_mx n (f : {ffun 'I_n -> bool}) :
  bdiag_mx f \is 0.-sunitary.
Proof.
apply/andP; split; last first.
  apply/forallP => i; apply/forallP=> j; rewrite !mxE.
  by rewrite mul1r rpredMn // rpredX // rpredN rpred1.
apply/mxunitaryP=> i j.
rewrite (bigD1 i) //= !mxE eqxx mulr1n.
rewrite eq_sym big1 ?addr0 => [|j1 Hj1].
  case:eqP=> [->|]; last by rewrite !mulr0n conjC0 mulr0.
  by rewrite !mulr1n -normCK  normr_sign expr1n.
by rewrite !mxE eq_sym (negPf Hj1) mulr0n mul0r.
Qed.

Lemma mxounitary_bdiag_mx n (f : {ffun 'I_n.+1 -> bool}) :
   bdiag_mx f  \is 0.-unitary.
Proof. by rewrite mxounitaryE mxsunitary0_odd mxsunitary_bdiag_mx. Qed.

Lemma mxsunitary_pair_OSK n (p : 'S_n * _) : 
   perm_mx p.1 *m bdiag_mx p.2 \is 0.-sunitary.
Proof.
by rewrite -{2}[0%N]addn0 mxsunitaryM // 
           ?mxsunitary_perm_mx ?mxsunitary_bdiag_mx.
Qed.

Lemma mxounitary_pair_OSK n (p : 'S_n.+1 * _) : 
   perm_mx p.1 *m bdiag_mx p.2 \is 0.-unitary.
Proof. by rewrite mxounitaryE mxsunitary0_odd  mxsunitary_pair_OSK. Qed.

Definition OSK0_enum n := 
  [seq OSKof (mxounitary_pair_OSK p) |
    p <- enum (Finite.clone _ ('S_n.+1 * {ffun 'I_n.+1 -> bool})%type)].

Lemma OSK0_enum_uniq n : uniq (OSK0_enum n).
Proof.
rewrite map_inj_uniq ?enum_uniq //.
move=> [p1 f1] [p2 f2] /val_eqP/eqP/matrixP /= H.
have Hp : p1 == p2.
  apply/eqP/permP=> i.
  have := H i (p1 i).
  rewrite !mxE (bigD1 (p1 i)) //= 
          !mxE eqxx mul1r mulr1n big1 ?addr0 => [|i1 Hi1].
    rewrite (bigD1 (p2 i)) //= !mxE eqxx mul1r big1 ?addr0 => [|i2 Hi2].
      by case: eqP=> // _ /eqP; rewrite mulr0n; case: (f1 _); 
           rewrite ?expr0 ?expr1 ?oppr_eq0 oner_eq0.
    by rewrite !mxE eq_sym (negPf Hi2) mul0r.
  by rewrite !mxE eq_sym (negPf Hi1) mul0r.
apply/pair_eqP; rewrite /= Hp /=.
apply/eqP/ffunP=> i.
have /eqP := H (p1^-1%g i) i.
  rewrite !mxE (bigD1 i) //= !mxE eqxx mulr1n /=.
have /permP/(_ i) H1 := mulVg p1; rewrite !permE in H1.
  rewrite [p1 _]H1 eqxx mul1r big1 ?addr0 => [|i1 Hi1].
  rewrite (bigD1 i) //= !mxE -(eqP Hp) [p1 _]H1 eqxx mul1r mulr1n.
  rewrite big1 ?addr0 => [|i2 Hi2].
    by case: (f1 i); case: (f2 i);
      rewrite ?expr0 ?expr1 // -subr_eq0 ?opprK -?opprD ?oppr_eq0 (eqC_nat 2 0).
  by rewrite !mxE [p1 _]H1 eq_sym (negPf Hi2) mul0r.
by rewrite !mxE [p1 _]H1 eq_sym (negPf Hi1) mul0r.
Qed.

Lemma mem_OSK0_enum n M : M \in (OSK0_enum n).
Proof.
pose p := perm (mcol_nz_inj (OSKs M)).
suff <-: OSKof (mxounitary_pair_OSK  (p,
                                   [ffun i => M ((p^-1)%g i) i != 1])) = M.
  by rewrite map_f // mem_enum.
apply/val_eqP/eqP/matrixP=> i j.
rewrite !mxE /=.
rewrite (bigD1 ((mcol_nz M) i)) //= !mxE permE ffunE eqxx mul1r.
rewrite big1 ?addr0 => [|i1 Hi1]; last first.
  by rewrite !mxE permE eq_sym ffunE (negPf Hi1) mul0r.
case : (_ =P j) => [H|/eqP H]; last first.
  by rewrite mulr0n mcol_nz_eq0 ?OSKs // eq_sym ffunE.
rewrite mulr1n -[in RHS]H.
have H2 : mcol_nz M i = p i by rewrite permE.
rewrite ffunE in H2.
have /permP/(_ i) H1 := mulgV p; rewrite !permE in H1.
rewrite ffunE H2 [(p^-1)%g  _]H1 -H2.
have /orP[/eqP|/eqP] := (mcol_nz_eq1 i (OSKs M)); rewrite ffunE => ->.
  by rewrite eqxx.
by rewrite eq_sym -subr_eq0 opprK (eqC_nat 2 0).
Qed.

Definition OSK0_uniq_enumP n : Finite.axiom _ := 
  Finite.uniq_enumP (OSK0_enum_uniq n) (@mem_OSK0_enum n).

HB.instance Definition _ n := isFinite.Build (OSK n.+1 0) (@OSK0_uniq_enumP n).

Lemma card_OSK0 n : #|OSK n.+1 0| = (n.+1`! * 2^n.+1)%N.
Proof.
rewrite cardT enumT unlock /= size_map -cardT.
rewrite card_prod card_ffun card_bool card_ord.
suff -> : #|(Finite.clone _ 'S_n.+1)| = #|perm_on [set: 'I_n.+1]|.
  by rewrite card_perm cardsT card_ord.
apply: eq_card => i.
apply/sym_equal.
rewrite !inE; apply/idP/subsetP=> j.
by rewrite !inE.
Qed.

Lemma s2int_det n k (M : OSK n k) : (sqrtC 2%:R) ^+ (k * n) * \det M \in s2Int.
Proof.
have H i j := mxsunitary_s2int i j (OSKs M).
rewrite mulr_sumr rpred_sum => //= i _.
rewrite mulrCA exprM /= -[X in _ ^+ _ ^+ X]card_ord -prodr_const /=.
rewrite -big_split /=.
by rewrite rpredM ?rpred_prod // rpredX // rpredN rpred1.
Qed.

Lemma s2int_det2_eq n k (M : OSK n k) : \det M ^+2 = 1.
Proof.
have /andP[/eqP H1 _] := OSKs M.
rewrite expr2 -{2}det_tr -trCmx_tr=> [|i j]; last first.
  have F : (sqrtC 2%:R) ^+ k != 0 :> algC.
    by rewrite expf_neq0 // sqrtC_eq0 (eqC_nat _ 0).
  rewrite -[M _ _](mulfK F) [M _ _ * _]mulrC rpredM //.
    by rewrite Creal_s2Int // mxsunitary_s2int // OSKs.
  by rewrite rpredV rpredX // Creal_s2Int // sQ2_proof.
by rewrite -det_mulmx H1 det_scalar expr1n.
Qed.

Lemma s2int_det_eq n k (M : OSK n k) : (\det M == 1) || (\det M == -1).
Proof. by rewrite -eqf_sqr s2int_det2_eq expr1n. Qed.

Lemma s2int_det_neq0 n k (M : OSK n k) : \det M != 0.
Proof.
by case/orP : (s2int_det_eq M) => /eqP->; rewrite ?oppr_eq0 oner_neq0.
Qed.

Definition POSK {n k} := [pred M : OSK n k | \det M > 0].
Definition NOSK {n k} := [pred M : OSK n k | \det M < 0].

Lemma POSK_NOSK n k (M : OSK n k) : NOSK M = ~~ (POSK M).
Proof.
rewrite /= real_ltNge ?lt_neqAle  //.
  by rewrite eq_sym ?s2int_det_neq0.
case/orP : (s2int_det_eq M) => /eqP-> //.
by rewrite rpredN /= -[_ \in _]/(_ \is Num.real).
Qed.

Lemma mxsunitary_swap n k (M : OSK n k) : 
  M *m bdiag_mx [ffun i : 'I_n => (0%N == i :> nat)] \is k.-sunitary.
Proof.
rewrite -{2}[k]addn0 mxsunitaryM //.
apply: OSKs.
apply: mxsunitary_bdiag_mx.
Qed.

Lemma mxounitary_swap n k (M : OSK n k) : 
  M *m bdiag_mx [ffun i : 'I_n => (0%N == i :> nat)] \is k.-unitary.
Proof.
rewrite mxounitaryE mxsunitary_swap /=.
case/mxoddP: (OSKo M) => i [j HO].
apply/mxoddP; exists i; exists j.
rewrite !mxE (bigD1 j) //= !mxE eqxx mulr1n !ffunE big1 => /= [|j1 j1Dj].
  rewrite addr0 mulrA odds2iM ?HO ?(mxsunitary_s2int _ _ (OSKs M)) // 1?andbC.
    by case: eqP; rewrite ?(expr1, expr0, odds2iN, odds2i_nat 1, rpred1).
  by rewrite rpredX // rpredN1.
by rewrite !mxE (negPf j1Dj) mulr0n mulr0.
Qed.

Definition bdiag_swap n k (M : OSK n.+1 k) := OSKof (mxounitary_swap M).

Lemma bdiag_swap_inj n k : injective (@bdiag_swap n k).
Proof.
move=> m1 m2 H; apply/val_eqP=> /=.
rewrite -[OSKm m1]mulmx1.
pose m3 := OSKof (mxounitary_bdiag_mx 
                    [ffun i : 'I_n.+1 => (0%N == i :> nat)]).
have H1 : 1%:M = m3 *m m3.
  by apply/matrixP=> i j; rewrite -bdiagM !mxE !ffunE addbb expr0.
rewrite H1 mulmxA [m1 *m m3]/(OSKm (bdiag_swap m1)) H.
by rewrite -mulmxA -[_ *m m3]H1 mulmx1.
Qed.

Lemma POSK_NOSK_swap n k (M : OSK n.+1 k) : 
   POSK  (bdiag_swap M) = ~~ POSK M.
Proof.
rewrite /= det_mulmx det_diag (bigD1 0) //= !mxE !ffunE expr1.
rewrite big1 => [|i nZi]; last first.
  by rewrite !mxE ffunE eq_sym; case: i nZi => [] [].
rewrite mulr1 mulrN1 oppr_gt0.
rewrite /= real_ltNge ?lt_neqAle  //.
  by rewrite eq_sym ?s2int_det_neq0.
case/orP : (s2int_det_eq M) => /eqP-> //.
by rewrite ?rpredN -[_ \in _]/(_ \is Num.real).
Qed.

Lemma card_OSK30 : #|OSK 3 0| = 48%N.
Proof. by rewrite card_OSK0. Qed.

Definition inOSK k (M : 'M[algC]_3) : OSK 3 k :=
  match M \is k.-unitary =P true with
  | ReflectT H => OSKof H
  | _ => OSKof (mxounitary_Tn k)
  end.

Lemma inOSKE  k (M : 'M[algC]_3) : M \is k.-unitary -> inOSK k M = M :> 'M_ _.
Proof. by rewrite /inOSK; case: eqP. Qed.

Definition OSK1_enum :=
  let l := enum (OSK 3 0) in
  [seq inOSK 1 (Tx *m (OSKm M)) | M <- l] ++
  [seq inOSK 1 (Ty *m (OSKm M)) | M <- l] ++
  [seq inOSK 1 (Tz *m (OSKm M)) | M <- l].

Lemma OSK1_enum_uniq : uniq OSK1_enum.
Proof.
have UM := enum_uniq (OSK 3 0).
rewrite cat_uniq map_inj_in_uniq ?enum_uniq /= => [|M1 M2 _ _ H]; last first.
  apply/val_eqP/eqP.
  apply: mxsunitary_inj (mxounitary_sunitary mxounitary_Tx) _.
  rewrite -[Tx *m _](inOSKE (mxounitary0_Tx (OSKos M1))) H.
  by rewrite (inOSKE (mxounitary0_Tx (OSKos M2))).
apply/andP; split=> //.
  apply/hasPn => /= M1; rewrite mem_cat => /orP[] /mapP[/= M2 _ HM2];
      apply/negP=> /mapP=> [] [/= M3 _ HM3].
    suff : erow 1 (M1 : 'M_ _) != erow 1 (M1 : 'M_ _) by rewrite eqxx.
    rewrite {1}HM2 {1}HM3 !inOSKE; last 2 first.
    - by apply/mxounitary0_Tx/OSKos.
    - by apply/mxounitary0_Ty/OSKos.
    by rewrite erow_Ty0 ?OSKos // ?erow_Tx0 ?OSKos.
  suff : erow 1 (M1 : 'M_ _) != erow 1 (M1 : 'M_ _) by rewrite eqxx.
  rewrite {1}HM2 {1}HM3 !inOSKE; last 2 first.
  - by apply/mxounitary0_Tx/OSKos.
  - by apply/mxounitary0_Tz/OSKos.
  by rewrite erow_Tz0 ?OSKos // ?erow_Tx0 ?OSKos.
(* This takes ages rewrite cat_uniq map_inj_in_uniq ?enum_uniq /= =>  *)
rewrite cat_uniq [X in [&& X, _ & _]]map_inj_in_uniq ?enum_uniq /= => 
    [|M1 M2 _ _ H]; last first.
  apply/val_eqP/eqP.
  apply: mxsunitary_inj (mxounitary_sunitary mxounitary_Ty) _.
  rewrite -[Ty *m _](inOSKE (mxounitary0_Ty (OSKos M1))) H.
  by rewrite (inOSKE (mxounitary0_Ty (OSKos M2))).
apply/andP; split=> //.
  apply/hasPn => M1 /mapP[M2 _ HM2];
      apply/negP=> /mapP=> [] [M3 _ HM3].
  suff : erow 1 (M1 : 'M_ _) != erow 1 (M1 : 'M_ _) by rewrite eqxx.
  rewrite {1}HM2 {1}HM3 !inOSKE; last 2 first.
  - by apply/mxounitary0_Ty/OSKos.
  - by apply/mxounitary0_Tz/OSKos.
  by rewrite erow_Tz0 ?OSKos // ?erow_Ty0 ?OSKos.
rewrite map_inj_in_uniq ?enum_uniq //= => [M1 M2 _ _ H].
apply/val_eqP/eqP.
apply: mxsunitary_inj (mxounitary_sunitary mxounitary_Tz) _.
rewrite -[Tz *m _](inOSKE (mxounitary0_Tz (OSKos M1))) H.
by rewrite (inOSKE (mxounitary0_Tz (OSKos M2))).
Qed.

Lemma mem_OSK1_enum (M : OSK 3 1) : M \in OSK1_enum.
Proof.
pose M' := OSKof (mxounitary_reduceT (OSKos M)).
have F : getM 1 M * trCmx (getM 1 M) == 1 by 
  case/or3P: (getME 1 M) => /eqP->/=;
  have [[/andP[Hx _]/andP[Hy _]]/andP[]]// := 
     (mxounitary_Tx, mxounitary_Ty, mxounitary_Tz).
have -> : M = inOSK 1 (getM 1 M * reduceT 1 M).
  apply/val_eqP; rewrite /=.
  rewrite /reduceT mulrA (eqP F) [_ * _]mul_scalar_mx.
  by rewrite scale1r ?(eqC_nat 2 0) // inOSKE // OSKos.
have /map_f F1 : OSKof (mxounitary_reduceT (OSKos M)) \in enum (OSK 3 0).
  by rewrite (mem_enum (OSK 3 0)).
by (rewrite !mem_cat; case/or3P: (getME 1 M) => /eqP->; apply/or3P);
   [apply: Or31| apply: Or32 | apply: Or33]; rewrite F1.
Qed.

Fixpoint OSKn_enum k :=
 if k is k1.+1 then
   if k1 is k2.+1 then
  let l := OSKn_enum k1 in
  [seq inOSK k2.+2 (Tx *m (OSKm M)) | 
      M <- l & erow k2.+1 (OSKm M) != 0] ++
  [seq inOSK k2.+2 (Ty *m (OSKm M)) | 
      M <- l & erow k2.+1 (OSKm M) != 1] ++
  [seq inOSK k2.+2 (Tz *m (OSKm M)) | 
      M <- l & erow k2.+1 (OSKm M) != o2]
 else
  OSK1_enum
 else
  OSK0_enum 2.
  
Lemma OSKn_enum_prop k :
  uniq (OSKn_enum k) /\ (forall x, x \in OSKn_enum k).
Proof.
elim: k => /= [|[|k] [UIH EIH]].
- split=> [|i]; first by exact: OSK0_enum_uniq.
  by exact: mem_OSK0_enum.
- split=> [|i]; first by exact: OSK1_enum_uniq.
  by exact: mem_OSK1_enum.
split.
  rewrite cat_uniq map_inj_in_uniq ?enum_uniq ?mem_filter => 
                  [|M1 M2]; last first.
    rewrite !mem_filter => /andP[H1 _] /andP[H2 _] H.
    apply/val_eqP/eqP.
    apply: mxsunitary_inj (mxounitary_sunitary mxounitary_Tx) _.
    have F1 : Tx * M1 \is k.+2.-unitary.
      by rewrite mxounitary_Tx_mul // OSKos.
    have F2 : Tx * M2 \is k.+2.-unitary.
      by rewrite mxounitary_Tx_mul // OSKos.
    by rewrite -[Tx *m _](inOSKE F1) H (inOSKE F2).
  apply/andP; split; first by apply: filter_uniq.
  apply/andP; split.
    apply/hasPn => M1; rewrite mem_cat => /orP[] /mapP[M2];
      rewrite !mem_filter => /andP[F2 _] HM2;
      apply/negP=> /mapP=> [] [M3]; rewrite mem_filter => /andP[F3 _] HM3.
      suff : erow k.+2 (M1 : 'M_ _) != erow k.+2 (M1 : 'M_ _) by rewrite eqxx.
      rewrite {1}HM2 {1}HM3 !inOSKE; last 2 first.
      - by rewrite mxounitary_Tx_mul // OSKos.
      - by rewrite mxounitary_Ty_mul // OSKos.
      by rewrite (erow_Ty (OSKos M2)) //  (erow_Tx (OSKos M3)).
    suff : erow k.+2 (M1 : 'M_ _) != erow k.+2 (M1 : 'M_ _) by rewrite eqxx.
    rewrite {1}HM2 {1}HM3 !inOSKE; last 2 first.
    - by rewrite mxounitary_Tx_mul // OSKos.
    - by rewrite mxounitary_Tz_mul // OSKos.
    by rewrite (erow_Tz (OSKos M2)) //  (erow_Tx (OSKos M3)).
  (* This takes ages rewrite cat_uniq map_inj_in_uniq ?enum_uniq /= => *)
  rewrite cat_uniq [X in [&& X, _ & _]]map_inj_in_uniq ?enum_uniq /= =>
     [|M1 M2]; last first.
    rewrite !mem_filter => /andP[F1 _] /andP[F2 _] H.
    apply/val_eqP/eqP.
    apply: mxsunitary_inj (mxounitary_sunitary mxounitary_Ty) _.
    have X1 : Ty * M1 \is k.+2.-unitary.
      by rewrite mxounitary_Ty_mul // OSKos.
    have X2 : Ty * M2 \is k.+2.-unitary.
      by rewrite mxounitary_Ty_mul // OSKos.
    by rewrite -[Ty *m _](inOSKE X1) H (inOSKE X2).
  apply/andP; split; first by apply: filter_uniq.
  apply/andP; split.
    apply/hasPn => M1 /mapP[M2];
      rewrite mem_filter => /andP[F2 _] HM2;
      apply/negP=> /mapP=> [] [M3]; 
      rewrite mem_filter => /andP[F3 _] HM3.
    suff : erow k.+2 (M1 : 'M_ _) != erow k.+2 (M1 : 'M_ _) by rewrite eqxx.
    rewrite {1}HM2 {1}HM3 !inOSKE; last 2 first.
    - by rewrite mxounitary_Ty_mul // OSKos.
    - by rewrite mxounitary_Tz_mul // OSKos.
    by rewrite (erow_Tz (OSKos M2)) //  (erow_Ty (OSKos M3)).
  rewrite map_inj_in_uniq ?enum_uniq ?filter_uniq //= => [M1 M2].
  rewrite !mem_filter => /andP[F1 _] /andP[F2 _] H.
  apply/val_eqP/eqP.
  apply: mxsunitary_inj (mxounitary_sunitary mxounitary_Tz) _.
  have X1 : Tz * M1 \is k.+2.-unitary.
    by rewrite mxounitary_Tz_mul // OSKos.
  have X2 : Tz * M2 \is k.+2.-unitary.
    by rewrite mxounitary_Tz_mul // OSKos.
  by rewrite -[Tz *m _](inOSKE X1) H (inOSKE X2).
move=> M.
pose M' := OSKof (mxounitary_reduceT (OSKos M)).
have F : getM k.+2 M * trCmx (getM k.+2 M) == 1%:M by 
  case/or3P: (getME k.+2 M) => /eqP->/=;
  have [[/andP[Hx _]/andP[Hy _]]/andP[]]// :=
     (mxounitary_Tx, mxounitary_Ty, mxounitary_Tz).
have ME : M = getM k.+2 M * reduceT k.+2 M :> 'M_ _.
  by rewrite /reduceT mulrA (eqP F) mul1r.
have -> : M = inOSK k.+2 (getM k.+2 M * reduceT k.+2 M).
  by apply/val_eqP/eqP; rewrite /= inOSKE // -ME OSKos.
have /map_f F1 : OSKof (mxounitary_reduceT (OSKos M)) \in OSKn_enum k.+1.
  by apply: EIH.
 (rewrite !mem_cat; case/or3P: (getME k.+2 M) => /eqP GH; apply/or3P);
   [apply: Or31| apply: Or32 | apply: Or33]; rewrite GH;
  apply/mapP; exists (OSKof (mxounitary_reduceT (OSKos M))) => //;
  rewrite mem_filter EIH andbT /=.
- by rewrite -(mxounitary_Tx_mul (mxounitary_reduceT (OSKos M))) -GH -ME OSKos.
- by rewrite -(mxounitary_Ty_mul (mxounitary_reduceT (OSKos M))) -GH -ME OSKos.
by rewrite -(mxounitary_Tz_mul (mxounitary_reduceT (OSKos M))) -GH -ME OSKos.
Qed.

Lemma OSKn_enum_uniq k : uniq (OSKn_enum k).
Proof. by case (OSKn_enum_prop k). Qed.

Lemma mem_OSKn_enum k M : M \in OSKn_enum k.
Proof. by case (OSKn_enum_prop k). Qed.

Definition OSKn_uniq_enumP k : Finite.axiom _ := 
  Finite.uniq_enumP (OSKn_enum_uniq k) (@mem_OSKn_enum k).

Definition OSK3 k := (OSK 3 k).
HB.instance Definition _ k := [Countable of OSK3 k by <:].
HB.instance Definition _ k := isFinite.Build (OSK3 k) (@OSKn_uniq_enumP k).

Lemma OSK_card k : #|OSK3 k| = (48 * (3 ^ (k != 0)) * 2 ^ (k.-1))%N.
Proof.
elim: k => [|[|k]].
- by rewrite !expn0 !muln1 -[48%N](card_OSK0 2) !cardT !enumT unlock.
- rewrite !cardT !enumT /= expn1 !muln1 unlock /= => IH.
  by rewrite !size_cat !{1}size_map unlock addnn -muln2 -mulnS -IH.
have ->: #|OSK3 k.+2| = 
        size (let l := OSKn_enum k.+1 in
  [seq inOSK k.+2 (Tx *m (OSKm M)) |
      M <- l & erow k.+1 (OSKm M) != 0] ++
  [seq inOSK k.+2 (Ty *m (OSKm M)) | 
      M <- l & erow k.+1 (OSKm M) != 1] ++
  [seq inOSK k.+2 (Tz *m (OSKm M)) | 
      M <- l & erow k.+1 (OSKm M) != o2]).
  by rewrite cardT !enumT  unlock.
rewrite !size_cat !{1}size_map !{1}size_filter expn1 => H.
set u := OSKn_enum _.
pose f  i  := fun M : OSK 3 k.+1 => erow k.+1 (M : 'M_ _) != i.
pose g i  := fun M : OSK 3 k.+1 => erow k.+1 (M : 'M_ _) == i.
have F v: count (f v) u = 
   (count (g (inZp (v + 1))) u + count (g (inZp (v + 2))) u)%N.
  rewrite -count_predUI -[LHS]addn0; congr addn.
    apply: eq_count => i; rewrite /f /g /=.
    by case/or3P : (o3E (erow k.+1 (i : 'M__))) => /eqP->;
       case/or3P : (o3E v) => /eqP->//=.
  rewrite -(@eq_count _ pred0) ?count_pred0 // => i /=.
  by rewrite /g; case: eqP => // ->;
     case/or3P : (o3E v) => /eqP->//=.
rewrite !F /=.
set a1 := count _ _; set a2 := count _ _; set a3 := count _ _.
apply: etrans (_ : 2 * (a1 + a2 + a3) = _)%N.
  rewrite mulSn mul1n -!addnA; congr (_ + ( _ + _))%N.
  by rewrite addnC -!addnA; congr addn; rewrite addnC addnA.
rewrite -addnA -count_predUI addnA -count_predUI.
rewrite -(@eq_count _ predT) ?count_predT  => [|i /=]; last first.
  by rewrite /g; case/or3P : (o3E (erow k.+1 (i : 'M_ _))) => /eqP->.
rewrite -(@eq_count _ pred0) ?count_pred0  => [|i /=]; last first.
  by rewrite /g; case/or3P : (o3E (erow k.+1 (i : 'M_ _))) => /eqP->.
rewrite -(@eq_count _ pred0) ?count_pred0  => [|i /=]; last first.
  by rewrite /g; case/or3P : (o3E (erow k.+1 (i : 'M_ _))) => /eqP->.
rewrite !addn0 (_ : size u = #|OSK3 k.+1|).
  by rewrite mulnC H -!mulnA -expnSr.
by rewrite cardT enumT unlock.
Qed.

Definition POSK3 k : pred (OSK3 k) := @POSK 3 k.

Lemma POSK_card k : #|@POSK3 k| = (24 * (3 ^ (k != 0)) * 2 ^ (k.-1))%N.
Proof.
apply: double_inj.
rewrite -addnn -mul2n !mulnA -OSK_card {2}(_ : #|@POSK3  k| = #|predC (@POSK3 k)|).
  rewrite -cardUI -(@eq_card _ predT) => [|i]; last first.
    by rewrite !inE /= [X in ~~ X]inE; case: (_ < _).
  rewrite OSK_card -(@eq_card _ pred0) ?card0 ?addn0 // => i.
  by rewrite !inE /= [X in ~~ X]inE; case: (_ < _).
pose f (M : OSK3 k) : OSK3 k := inOSK k (- (OSKm M)).
have /card_imset<-: injective f.
  move=> M1 M2 /val_eqP/eqP /=.
  rewrite !inOSKE ?mxounitaryN ?OSKos // => HH.
  apply/val_eqP/eqP.
  by rewrite -[LHS]opprK HH opprK.
pose NO : pred (OSK3 k) := NOSK.
  apply: etrans (_ : #|NO| = _); last first.
  by apply: eq_card => i; rewrite [_ \in _]POSK_NOSK.
apply: eq_card => i; rewrite !inE /=.
apply/imsetP/idP=> [[M1 HM1 ->] |H].
  rewrite /f inOSKE ?mxounitaryN ?OSKos //.
  rewrite -scaleN1r detZ !exprS expr0 !(mulNr, mul1r) !opprK.
  by rewrite oppr_lt0.
exists (f i); last first.
  rewrite /f inOSKE ?opprK ?mxounitaryN ?OSKos //.
  by apply/val_eqP; rewrite /= inOSKE ?OSKos.
rewrite !inE /f inOSKE ?mxounitaryN ?OSKos //.
rewrite -scaleN1r detZ !exprS expr0 !(mulNr, mul1r) !opprK.
by rewrite oppr_gt0.
Qed.

(* Some facts *)

Lemma addr2K (R : zmodType) (x y z : R) : (x + y == x + z) = (y == z).
Proof.
by rewrite -[in LHS]subr_eq0 opprD addrA [x + _]addrC addrK subr_eq0. 
Qed.

Lemma i1E (i : 'I_1) : i == 0.
Proof. by case: i => [] []. Qed.

Lemma i2E (i : 'I_2) : (i == 0) || (i == 1).
Proof. by case: i => [] [|[]]. Qed.

Definition o2 := Ordinal (isT: 2 < 3)%N.

Lemma i3E (i : 'I_3) : [|| i == 0, i == 1 | i == o2].
Proof. by case: i => [] [|[|[]]]. Qed.

Lemma i32E (i j : 'I_3) : [||i == j, i == j - 1| i == j + 1].
Proof. by case/or3P: (i3E i)=> /eqP->; case/or3P: (i3E j)=> /eqP-> //=. Qed.

Lemma s3E (R : zmodType) (F : 'I_3 -> R) :
       \sum_(i < 3) F i = F 0 + F 1 + F o2.
Proof. 
rewrite !big_ord_recl !big_ord0 !addrA addr0 /=.
by congr (F _ + F _ + F _); apply/val_eqP.
Qed.

Lemma s2E (R : zmodType) (F : 'I_2 -> R) :
       \sum_(i < 2) F i = F 0 + F 1.
Proof. 
rewrite !big_ord_recl !big_ord0 addr0 /=.
by congr (F _ + F _ ); apply/val_eqP.
Qed.

Local Notation "''M{' l } " := (seq2matrix _ _ l).

(* Pauli operators *)
Definition Px :'M[algC]_2 := 'M{[::[::0 ;  1]; 
                                   [::1 ;  0]]}.
 
Definition Py :'M[algC]_2 := 'M{[::[:: 0 ;  -'i]; 
                                   [::'i ;   0]]}.

Definition Pz :'M[algC]_2 := 'M{[::[:: 1 ;   0]; 
                                   [:: 0 ;  -1]]}.

Definition Pauli i := tnth [tuple of [::Px; Py; Pz]] i. 
Local Notation "'P_ i" := (Pauli i) (at level 10).

Lemma Pauli_prod i j : 'P_i * 'P_j = 
    if  i == j then 1 else ((-1) ^+ (j != i + 1) * 'i) *: 'P_(-(i + j)).
Proof.
by case/or3P : (i3E i) => {i}/eqP->; case/or3P : (i3E j) => {j}/eqP->;
 apply/matrixP=> i j;
 rewrite !mxE s2E !mxE /=;
 case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
 rewrite /= ?(add0r, addr0, mul0r, mulr0, mul1r, mulr1, mulNr, mulrN) //
                  -?expr2 ?sqrCi ?opprK ?oppr0.
Qed.

Lemma Pauli_nilpotent i : 'P_i * 'P_i = 1.
Proof. by rewrite Pauli_prod eqxx. Qed.

Lemma Pauli_sym i j : 'P_j * 'P_i = (-1) ^+ (i != j) *: ('P_i * 'P_j).
Proof.
rewrite !Pauli_prod [j == _]eq_sym.
case/or3P : (i32E i j)=> /eqP->;
  rewrite ?eqxx ?scale1r //= -subr_eq0 [j + _]addrC addrK //=.
  by rewrite addrC addr2K /= subrK eqxx /= addrC !scalerA mul1r.
rewrite mul1r addrC !scalerA mulrA -exprD.
congr (_ *: _).
by rewrite -addrAC eq_sym -subr_eq0 addrK add1n expr2 mulNr mul1r opprK mul1r.
Qed.

Lemma Pauli_base M :
  2%:R *: M = (\tr M)%:M + \sum_(i < 3) \tr('P_i * M) *: 'P_i.
Proof.
rewrite s3E /Pauli !(tnth_nth 0) /=.
apply/matrixP=> i j.
case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->; 
  rewrite /mxtrace !(s2E, mxE) /= 
  ?(mulNr, mulrN, opprK, mul0r, mulr0, mulr1n, addr0, add0r, mul1r, mulr1).
- by rewrite -addrA [M 1 1 + _]addrC subrK mulrDl mul1r.
- rewrite [_ * 'i]mulrC mulrDr mulrN !mulrA -expr2 sqrCi !mulNr !mul1r opprK.
  by rewrite opprB addrC addrA subrK mulrDl mul1r.
- rewrite [_ * 'i]mulrC mulrDr mulrN !mulrA -expr2 sqrCi !mulNr !mul1r opprK.
  by rewrite -addrA [M 0 1 + _]addrC subrK mulrDl mul1r.
by rewrite opprB [RHS]addrC !addrA subrK mulrDl mul1r.
Qed.

Lemma trIE (M: 'M[algC]_2) : \tr M = M 0 0 + M 1 1.
Proof. by rewrite /mxtrace s2E. Qed.

Lemma trXE (M: 'M[algC]_2) : \tr ('P_0 * M) = M 0 1 + M 1 0.
Proof. 
rewrite /mxtrace s2E !mxE !s2E /Pauli !(tnth_nth 0) !mxE /=.
by rewrite !mul1r !mul0r add0r addr0 addrC.
Qed.

Lemma trYE (M: 'M[algC]_2) : \tr ('P_1 * M) = 'i * (M 0 1 - M 1 0).
Proof. 
rewrite /mxtrace s2E !mxE !s2E /Pauli !(tnth_nth 0) !mxE /=.
by rewrite !mul0r add0r addr0 mulrBr addrC mulNr.
Qed.

Lemma trZE (M: 'M[algC]_2) : \tr ('P_o2 * M) = M 0 0 - M 1 1.
Proof. 
rewrite /mxtrace s2E !mxE !s2E /Pauli !(tnth_nth 0) !mxE /=.
by rewrite !mul0r add0r addr0 !mul1r mulNr mul1r.
Qed.

Notation "M ^T*" := (trCmx M) (at level 10).

Lemma Pauli_trcmX i : 'P_i ^T* = 'P_i.
Proof.
by case/or3P : (i3E i) => /eqP->; 
  rewrite /Pauli  !(tnth_nth 0) /=; 
  apply/matrixP=> i1 j1; 
  case/orP : (i2E i1) => /eqP->; 
  case/orP : (i2E j1) => /eqP->; 
  repeat rewrite ?mxE /= ?(opprK, raddf0, rmorph1, raddfN, conjCi).
Qed.

Lemma Pauli_hermit i : 'P_i * ('P_i) ^T* = 1.
Proof. by rewrite Pauli_trcmX Pauli_prod eqxx. Qed.

Lemma is_unitary2l (M : 'M[algC]_2) :
  M \is mxunitary -> 
 [/\ M 0 0 * (M 1 0)^* + M 0 1 * (M 1 1)^* = 0,
     M 1 0 * (M 0 0)^* + M 1 1 * (M 0 1)^* = 0,
     M 0 0 * (M 0 0)^* + M 0 1 * (M 0 1)^* = 1 &
     M 1 0 * (M 1 0)^* + M 1 1 * (M 1 1)^* = 1
  ].
Proof.
rewrite qualifE => /eqP H; split.
- have <-: (M *m M^T* ) 0 1 = 0 by rewrite H !mxE.
  by rewrite !mxE s2E !mxE.
- have <-: (M *m M^T* ) 1 0 = 0 by rewrite H !mxE.
  by rewrite !mxE s2E !mxE.
- have <-: (M *m M^T* ) 0 0 = 1 by rewrite H !mxE.
  by rewrite !mxE s2E !mxE.
have <-: (M *m M^T* ) 1 1 = 1 by rewrite H !mxE.
by rewrite !mxE s2E !mxE.
Qed.

Lemma is_unitary2r (M : 'M[algC]_2) :
  M \is mxunitary -> 
 [/\ M 0 0 * (M 0 1)^* + M 1 0 * (M 1 1)^* = 0,
     M 0 1 * (M 0 0)^* + M 1 1 * (M 1 0)^* = 0,
     M 0 0 * (M 0 0)^* + M 1 0 * (M 1 0)^* = 1 &
     M 0 1 * (M 0 1)^* + M 1 1 * (M 1 1)^* = 1
  ].
Proof.
rewrite -mxunitaryT qualifE trCmxK=> /eqP H; split.
- have <-: (M^T* *m M) 1 0 = 0 by rewrite H !mxE.
  by rewrite !mxE s2E !mxE ![_^* * _]mulrC.
- have <-: (M^T* *m M) 0 1 = 0 by rewrite H !mxE.
  by rewrite !mxE s2E !mxE ![_^* * _]mulrC.
- have <-: (M^T* *m M) 0 0 = 1 by rewrite H !mxE.
  by rewrite !mxE s2E !mxE ![_^* * _]mulrC.
have <-: (M^T* *m M) 1 1 = 1 by rewrite H !mxE.
by rewrite !mxE s2E !mxE ![_^* * _]mulrC.
Qed.

Lemma Pauli_unitary i : 'P_ i \in mxunitary.
Proof. 
by rewrite qualifE Pauli_trcmX [_ *m _]Pauli_prod !eqxx.
Qed.

Definition Mlift (M : 'M[algC]_2) : 'M[algC]_3 :=
  'M{
  [::
    [:: 'Re (M 0 1 * (M 1 0)^* + M 0 0 * (M 1 1)^*);
       -'Im (M 0 1 * (M 1 0)^* - M 0 0 * (M 1 1)^*);
        'Re (M 0 1 * (M 1 1)^*) *- 2];
    [:: 'Im (M 1 1 * (M 0 0)^* + M 1 0 * (M 0 1)^*);
       -'Re (M 1 0 * (M 0 1)^* - M 1 1 * (M 0 0)^*);
        'Im  (M 0 1 * (M 1 1)^*) *+ 2 ];
    [:: 'Re (M 0 1 * (M 0 0)^*) *+ 2;
        'Im (M 0 1 * (M 0 0)^*) *- 2;
        M 0 0* (M 0 0)^* - M 0 1 * (M 0 1)^*
    ]
  ]}.

Definition Cl :=
  (opprB, opprD, mulNr, mulrN, conjC0, conjC1, raddf0, rmorph1,
   raddfN, mul0rn,
   addr0, add0r, mul0r, mulr0, mul1r, mulr1, oppr0, @opprK).

Lemma Mlift1 : Mlift 1 = 1.
Proof.
apply/matrixP=> i j.
by case/or3P : (i3E i) => {i}/eqP->;
  case/or3P : (i3E j) => {j}/eqP->;
  rewrite !mxE /= !Cl /= ?(Creal_ReP _ _) ?(Creal_ImP _ _).
Qed.

Lemma MliftT : {in mxunitary, {morph Mlift : x / x^T* }}.
move=> M H.
apply/matrixP=> i j.
case/or3P : (i3E i) => {i}/eqP->;
  case/or3P : (i3E j) => {j}/eqP->;
  rewrite !mxE /= ?[('Re _)^*]conj_Creal ?[('Im _)^*]conj_Creal 
        ?Creal_Re ?Creal_Im //. 
- rewrite !raddfD /= mulrC !conjCK; congr (_ + _).
  by rewrite -[LHS]Re_conj /= !rmorphM conjCK.
- rewrite raddfB /= opprB !conjCK.
  rewrite !raddfD /= mulrC ; congr (_ + _).
  by rewrite -[LHS]Im_conj rmorphM conjCK.
- rewrite  /= !conjCK.
  have [_] := is_unitary2r H.
  move=>/eqP; rewrite mulrC addr_eq0 => /eqP-> _ _.
  rewrite [in RHS]raddfMn /= [('Re _)^*]conj_Creal ?Creal_Re //=.
  by rewrite raddfN /= mulNrn mulrC.
- rewrite !conjCK ![in RHS]raddfN /=.
  rewrite [('Im _)^*]conj_Creal ?Creal_Im //.
  rewrite raddfB raddfD /= opprB.
  rewrite -![in RHS]Im_conj mulrC; congr (_ + _).
  by rewrite rmorphM conjCK.
- rewrite raddfN /= [('Re _)^*]conj_Creal ?Creal_Re //=.
  rewrite !conjCK !raddfD /= mulrC; congr (_ + _).
  by rewrite -[in LHS]Re_conj raddfN /= !rmorphM !conjCK.
- rewrite !conjCK ![in RHS]raddfMn /= raddfN /=.
  rewrite [('Im _)^*]conj_Creal ?Creal_Im //=.
  have [_] := is_unitary2r H.
  move=>/eqP; rewrite addr_eq0 => /eqP-> _ _.
  by rewrite mulrC raddfN /= opprK.
- rewrite !conjCK ![in RHS]raddfMn /= raddfN /=.
  have [] := is_unitary2l H.
  move=>/eqP; rewrite mulrC addr_eq0 => /eqP-> _ _ _.
  by rewrite raddfN /= [('Re _)^*]conj_Creal ?Creal_Re.
- rewrite !conjCK ![in RHS]raddfMn /=.
  have [] := is_unitary2l H.
  move=>/eqP; rewrite mulrC addr_eq0 => /eqP-> _ _ _.
  rewrite raddfN /= [('Im _)^*]conj_Creal ?Creal_Im //.
  by rewrite raddfMn /= opprK.
rewrite !conjCK raddfB /= !rmorphM !conjCK ![_^* * _]mulrC.
apply/eqP; rewrite subr_eq addrC addrA eq_sym subr_eq; apply/eqP.
have [_ _ _] := is_unitary2l H.
move=>/eqP; rewrite eq_sym -subr_eq => /eqP<-.
have [_ _ _] := is_unitary2r H.
move=>/eqP; rewrite eq_sym -subr_eq => /eqP<-.
by rewrite addrC.
Qed.

Definition Dl :=
  (mulrBr, mulrDr, mulrBl, mulrDl, opprB, opprD, mulNr, mulrN, @opprK,
   mulrA, addrA).

Lemma MliftE M (ci co : 'cV_3) : 
  M \is mxunitary -> 
    (Mlift M *m ci == co) = 
   (M * (\sum_k (ci k 0 *: 'P_k)) * M^T* == \sum_k (co k 0 *: 'P_k)).
Proof.
move=> H.
have FR (x : algC) : 'Re x *+ 2 = x + x^*.
  by rewrite -mulr_natr /= /Re unlock divfK ?(eqC_nat _ 0).
have FI (x : algC) : 'Im x *+ 2 = 'i * (x^* - x).
  by rewrite -mulr_natr /Im unlock divfK ?(eqC_nat _ 0).
have FNI : ((forall x : algC, 'i * x = x *'i)%R *
                 (forall x y: algC, x * 'i * y = x * y *'i)%R *
                 (forall x y z: algC, x * y * 'i * z = x * y * z *'i)%R)%type.
  by split; [split |] => *;
     do 3 (rewrite-?mulrA //; try (congr (_ * _); [idtac]) || rewrite mulrC).
have FNC : (forall x, (forall y : algC , x * y = y * x)%R *
            (forall y z : algC, y * x * z =  y * z * x)%R)%type.
  by split => *;
     do 5 (rewrite-?mulrA //; try (congr (_ * _); [idtac]) || rewrite mulrC).
set x := ci 0 0; set y := ci 1 0; set z := ci o2 0.
have FNCC := (FNC x, FNC y, FNC z).
have S1 : M 1 0 * (M 1 1)^* = - (M 0 0 * (M 0 1)^*).
  rewrite -[LHS]conjCK rmorphM conjCK mulrC.
  have [_] := is_unitary2r H.
  move=>/eqP; rewrite addrC addr_eq0=>/eqP-> _ _.
  by rewrite raddfN /= rmorphM conjCK mulrC.
have S2 : M 0 1 * (M 1 1)^* = - (M 0 0 * (M 1 0)^*).
  rewrite -[LHS]conjCK rmorphM conjCK mulrC.
  have [_] := is_unitary2l H.
  move=>/eqP; rewrite addrC addr_eq0=>/eqP-> _ _.
  by rewrite raddfN /= rmorphM conjCK mulrC.
apply/eqP/eqP=> /matrixP H1; apply/matrixP=> i j.
- case/orP : (i2E i) => {i}/eqP->; case/orP : (i2E j) => {j}/eqP->;
    rewrite !(mxE, s2E, s3E)/= ?Cl;
    rewrite -?H1 !(mxE, s3E) /= -/x -/y -/z;
    rewrite !FR !FI ?raddfB ?raddfD !rmorphM /= mulrC
            !conjCK !Dl !FNI !FNCC ![_ ^* * _]mulrC.
  - by do 10 (rewrite-?addrA; try ((congr (_ + _); [idtac]) || rewrite addrC)).
  - rewrite -![_ * 'i * 'i]mulrA -expr2 sqrCi !Cl.
    rewrite S2 mulNr opprK.
    set X1 := _ * _ * x; set X2 := _ *'i * x.
    set X3 := _ * 'i * x; set X4 := _ * _ * x.
    set X5 := _ * x; set X6 := _ * x.
    set Y1 := _ * _ * y; set Y2 := _ * _ * y.
    set Y3 := _ * _ * y; set Y4 := _ * _ * y.
    set Y5 := 'Im (M 0 1 * (M 1 0)^*) * y; set Y6 := _ * y.
    set Z1 := _ * _ * z; set Z2 := _ * _ * z.
    apply: etrans
       (_ :  (Z2 - Z2) + Z1 + Z1 + (X6 - X2) + (X5 - X3) +
                (Y6 - Y4) + (Y3 -Y5) = _); last first.
      by do 60 (rewrite-?addrA; try ((congr (_ + _); [idtac]) || rewrite addrC)).
    rewrite subrr add0r -[X6 - X2]mulrBl -[- (_  * 'i)]mulNr -Im_conj rmorphM conjCK.
    rewrite [_^* * _]mulrC [_ * 'i]mulrC -algCrect -/X1.
    rewrite -[X5 - _]mulrBl -[-(_ * 'i)]mulNr -Im_conj rmorphM conjCK.
    rewrite [_^* * _]mulrC [_ * 'i]mulrC -algCrect -/X4.
    rewrite -[Y6 - _]mulrBl -['Im _]opprK -[-'Im _]mulrN1 -sqrCi expr2 mulrA.
    rewrite -mulNr -[_ - _ *'i]mulrBl -opprD -Re_conj rmorphM conjCK.
    rewrite [_ + 'Re _]addrC ['Im _ * 'i]mulrC [_^* * _]mulrC -algCrect.
    rewrite !mulNr -/Y2.
    rewrite -[Y3 - _]mulrBl -[-'Im _]mulrN1 -sqrCi expr2 mulrA.
    rewrite -[_ * 'i + _]mulrDl -Re_conj rmorphM conjCK.
    rewrite  ['Im _ * 'i]mulrC [_^* * _]mulrC -algCrect -/Y1.
    by do 20 (rewrite-?addrA; try ((congr (_ + _); [idtac]) || rewrite addrC)).
  - rewrite -![_ * 'i * 'i]mulrA -expr2 sqrCi !Cl.
    rewrite S2 mulNr opprK.
    have [_] := is_unitary2l H.
    move=>/eqP; rewrite addrC addr_eq0 => /eqP-> _ _ .
    rewrite /= !mulNr opprK.
    set X1 := _ * _ * x; set X2 := _ * _ * x.
    set X3 := _ * _ * x; set X4 := _ * _ * x.
    set X5 := _ * x; set X6 := _ * x.
    set Y1 := _ * _ * y; set Y2 := _ * _ * y.
    set Y3 := _ * _ * y; set Y4 := _ * _ * y.
    set Y5 := 'Im (M 0 1 * _) * y; set Y6 := _ * y.
    set Z1 := _ * _ * z; set Z2 := _ * _ * z.
    apply: etrans
       (_ :  (Z2 - Z2) + Z1 + Z1 + (X6 + X2) + (X5 + X3) -
                (Y5 + Y3) + (Y6 + Y4) = _); last first.
      rewrite opprD.
      by do 32 (rewrite-?addrA; try ((congr (_ + _); [idtac]) || rewrite addrC)).
    rewrite subrr add0r -[X6 + _]mulrDl -Re_conj rmorphM conjCK [_^* * _]mulrC.
    rewrite [_ * 'i]mulrC -algCrect -/X4.
    rewrite -[X5 + _]mulrDl -Re_conj rmorphM conjCK [_^* * _]mulrC.
    rewrite [_ * 'i]mulrC -algCrect -/X1.
    rewrite -[Y6 + _]mulrDl -Re_conj rmorphM conjCK [_^* * _]mulrC.
    rewrite -['Im _]opprK -[-'Im _]mulrN1 -sqrCi expr2 mulrA.
    rewrite -mulNr -[_ + _ *'i]mulrDl -[in RHS]mulNr -Im_conj rmorphM conjCK.
    rewrite [_ + 'Re _]addrC ['Im _ * 'i]mulrC [_^* * _]mulrC.
    rewrite -Re_conj rmorphM conjCK  [_^* * _]mulrC -algCrect -/Y1.
    rewrite -[Y5 + _]mulrDl -['Im _]opprK -[-'Im _]mulrN1 -sqrCi expr2 !mulrA.
    rewrite -[-(_ * 'i)]mulNr -[_ * 'i + _]mulrDl -[-(_ * 'i)]mulNr -Im_conj.
    rewrite rmorphM conjCK.
    rewrite [_ + 'Re _]addrC ['Im _ * 'i]mulrC [_^* * _]mulrC.
    rewrite -algCrect -/Y2.
    by do 20 (rewrite-?addrA; try ((congr (_ + _); [idtac]) || rewrite addrC)).
  - have [_] := is_unitary2r H.
    move=>/eqP; rewrite addrC addr_eq0 => /eqP-> _ _ .
    rewrite /= !mulNr.
    rewrite S1.
    rewrite /= !mulNr opprK.
    set X1 := M 0 0 * _ * x; set X2 := _ * _ * x.
    set Y1 := _ * 'i * y; set Y2 := _ * _ * y.
    set Z1 := _ * _ * z; set Z2 := M 0 1 * _ * z.
    set Z3 := M 0 0 * _ * z; set Z4 := _ * _ * z.
    do 9 (rewrite-?addrA; try ((congr (_ + _); [idtac]) || rewrite addrC)).
    apply/eqP; rewrite subr_eq addrC addrA -subr_eq; apply/eqP.
    rewrite opprK -!mulrDl addrC [in RHS]addrC; congr (_ * _).
    by have [_ _ -> ->] := is_unitary2r H.
rewrite /=.
case/or3P : (i3E i) => {i}/eqP->; rewrite {j} (eqP (i1E j)).
- suff : (Mlift M *m ci) 0 0 *+2  = co 0 0 *+2.
    by move/eqP; rewrite eqrMn2r => /eqP.
  rewrite ![in RHS]mulr2n  -{1}[co 0 0](subrK (co 1 0 * 'i)).
  rewrite -[RHS]addrA [_ * 'i + _]addrC.
  have := H1 0 1; rewrite !(mxE, s2E, s3E)/= ?Cl => <-.
  have := H1 1 0; rewrite !(mxE, s2E, s3E)/= ?Cl => <-.
  rewrite -/x -/y -/z.
  rewrite FR !(mulrnBl, mulrnDl) -2!mulrnAl FR FI !mulr2n.
  rewrite ?raddfB ?raddfD !rmorphM /= mulrC
            !conjCK !Dl !rmorphM !conjCK !FNI !FNCC.
  rewrite ![_^* * _]mulrC.
  rewrite S2 !mulNr !opprK.
  have [_] := is_unitary2l H.
  move=>/eqP; rewrite addrC addr_eq0 => /eqP-> _ _ .
  rewrite /= !mulNr opprK.
  set X1 := _ * _ * x; set X2 := _ * _ * x.
  set X3 := _ * _ * x; set X4 := _ * _ * x.
  set Y1 := _ * _ * y; set Y2 := _ * _ * y.
  set Y3 := _ * _ * y; set Y4 := _ * _ * y.
  set Z1 := _ * _ * z; set Z2 := _ * _ * z.
  by do 60 (rewrite-?addrA; try ((congr (_ + _); [idtac]) || rewrite addrC)).
- suff : ((Mlift M *m ci) 1 0 *'i) *+2   = (co 1 0  * 'i) *+2.
    by move/eqP; rewrite eqrMn2r /= =>/eqP /(mulIf (neq0Ci _)).
  rewrite ![in RHS]mulr2n  -{1}[co 1 0 * 'i](subrK (co 0 0)).
  rewrite -opprB -addrA.
  have FF := H1 0 1; rewrite !(mxE, s2E, s3E)/= ?Cl in FF; rewrite -{}FF.
  have FF := H1 1 0; rewrite !(mxE, s2E, s3E)/= ?Cl in FF; rewrite -{}FF.
  rewrite !(mxE, s2E, s3E)/= ?Cl -/x -/y -/z.
  rewrite FI -mulrnAl !(mulrnBl, mulrnDl).
   rewrite -[_ * x *+ 2]mulrnAl -[_ * y *+ 2]mulrnAl.
  rewrite FR FI !mulr2n.
  rewrite ?raddfB ?raddfD !rmorphM /= mulrC
            !conjCK !Dl !rmorphM !conjCK !FNI !FNCC.
  rewrite -![_ * 'i * 'i]mulrA -expr2 sqrCi !mulrN1.
  rewrite !FNI !FNCC ![_^* * _]mulrC !mulNr.
  rewrite S2.
  have [_] := is_unitary2l H.
  move=>/eqP; rewrite addrC addr_eq0 => /eqP-> _ _ .
  rewrite !mulNr !opprK.
  by do 60 (rewrite-?addrA; try ((congr (_ + _); [idtac]) || rewrite addrC)).
have := H1 0 0; rewrite !(mxE, s2E, s3E)/= ?Cl => <-.
rewrite FI FR -/x -/y -/z.
rewrite !Dl !rmorphM !conjCK !FNI !FNCC ![_^* * _]mulrC.
by do 20 (rewrite-?addrA; try ((congr (_ + _); [idtac]) || rewrite addrC)).
Qed.

(* Because of the formulation of MliftE that follows the article
   I have to reason on col instead of row. This is not what is 
   usually done in matrix *)
Lemma col_matrixP (R : Type) (m n : nat) (A B : 'M[R]_(m, n)) :
   (forall i : 'I_n, col i A = col i B) <-> A = B.
Proof.
split=> [eqAB | -> //]; apply/matrixP=> i j.
by move/colP/(_ i) : (eqAB j); rewrite !mxE.
Qed.

Lemma colE  (R : ringType) (m n : nat) (i : 'I_n) (A : 'M[R]_(m, n)) :
       col i A =  A *m delta_mx i 0.
Proof.
apply/colP=> j; rewrite !mxE (bigD1 i) //= mxE !eqxx mulr1.
by rewrite big1 ?addr0 // => i'  ne_i'i; rewrite mxE /= (negbTE ne_i'i) mulr0.
Qed.

Lemma MliftM : {in mxunitary &, {morph Mlift : x y / x *m y}}.
Proof.
move=> M1 M2 HM1 HM2.
apply/col_matrixP => i.
rewrite !colE.
apply/eqP; rewrite MliftE ?mxunitaryM //.
rewrite trCmx_mul !mulrA -[_ * M2^T* ]mulrA-[_ M2 * _ ]mulrA.
rewrite -[_ *m delta_mx _ _]mulmxA.
set co := _ *m delta_mx _ _.
have := eqxx co.
rewrite [M2 * _]mulrA.
rewrite MliftE //= => /eqP->.
have := eqxx (Mlift M1 *m co).
rewrite MliftE //= => /eqP->.
Qed.

Lemma MliftrM M i j : Mlift M i j \is Creal.
Proof.
case/or3P : (i3E i) => /eqP->; case/or3P : (i3E j) => /eqP->;
  rewrite !mxE ?(Creal_Re, Creal_Im, rpredN, rpredMn)//=.
by rewrite -!normCK rpredB // rpredX //;
   apply/CrealP; rewrite conj_normC.
Qed.

Lemma Mlift_unitary M : M \is mxunitary -> Mlift M \is mxunitary.
Proof.
move=> H.
rewrite qualifE -!MliftT // -!MliftM ?mxunitaryT //.
by rewrite (eqP H) Mlift1.
Qed.

Lemma trCmx_real m n (M : 'M_(m, n)) : 
  (forall i j, M i j \is Creal) -> M ^T* = M^T .
Proof.
move=> H.
by apply/matrixP=> i j; rewrite !mxE (CrealP _).
Qed.

(* Some common properties *)

Lemma sqrtC2_neq0 : sqrtC 2%:R != 0 :> algC.
Proof. by rewrite sqrtC_eq0 (eqC_nat _ 0). Qed.
Lemma sqrtC2_real : sqrtC 2%:R \is Creal.
Proof. by rewrite qualifE /= sqrtC_ge0 (ler_nat _ 0). Qed.
Lemma sqrtC2I_real : (sqrtC 2%:R)^-1 \is Creal.
Proof. by rewrite rpredV; exact: sqrtC2_real. Qed.

(* Hadamard matrix *)

Definition H : 'M[algC]_2 :=  (sqrtC 2%:R)^-1 *: 'M{[::[::1;1]; [::1; -1]]}.

Lemma H_unitary : H \is mxunitary.
Proof.
have [[Hs1 Hs2] Hs3] := (sqrtC2_neq0, sqrtC2_real, sqrtC2I_real).
by apply/eqP/matrixP=> i j;
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE, CrealP _) /= ?Cl;
   try (rewrite ?rpredN; exact: sqrtC2I_real);
   rewrite ?subrr // -invfM -expr2 sqrtCK -mulr2n -[_ *+ 2]mulr_natl 
           divff ?(eqC_nat _ 0).
Qed.

Lemma Hlift : Mlift H = 'M{[::[::0; 0; 1]; [::0; -1; 0]; [::1; 0; 0]]}.
Proof.
have [[Hs1 Hs2] Hs3] := (sqrtC2_neq0, sqrtC2_real, sqrtC2I_real).
apply/matrixP=> i j; 
 case/or3P : (i3E i) => /eqP->; case/or3P : (i3E j) => /eqP->;
  rewrite !mxE ?Cl //= (CrealP _) // ?subrr //.
- by rewrite raddf0.
- by rewrite (Creal_ImP _ _) ?(rpredD, rpredM) // Cl.
- rewrite (Creal_ReP _ _) ?(rpredD, rpredM) //.
  by rewrite -invfM -expr2 sqrtCK -mulr2n -[_ *+ 2]mulr_natl 
             divff ?(eqC_nat _ 0).
- by rewrite (Creal_ImP _ _) ?(rpredN, rpredD, rpredM).
- rewrite (Creal_ReP _ _) ?(rpredD, rpredM) //.
  by rewrite -invfM -expr2 sqrtCK -mulr2n -mulr_natl divff ?(eqC_nat _ 0).
- by rewrite (Creal_ImP _ _) ?(rpredD, rpredM) // ?Cl.
- rewrite (Creal_ReP _ _) ?(rpredD, rpredM) //.
  by rewrite -invfM -expr2 sqrtCK -mulr_natl divff ?(eqC_nat _ 0).
by rewrite (Creal_ImP _ _) ?(rpredD, rpredM) // ?Cl.
Qed.

(* Phase matrix *)

Definition S : 'M[algC]_2 := 'M{[::[::1;0]; [::0; 'i]]}.

Lemma S_unitary : S \is mxunitary.
Proof.
by apply/eqP/matrixP=> i j;
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) /= ?Cl // -1?[_^* * _]mulrC
           -normCK normCi expr2 Cl.
Qed.

Lemma Slift : Mlift S = 'M{[::[:: 0;-1; 0]; [:: 1; 0; 0]; [:: 0; 0; 1]]}.
Proof.
by apply/matrixP=> i j; 
   case/or3P : (i3E i) => /eqP->; case/or3P : (i3E j) => /eqP->;
   rewrite !mxE ?Cl //= ?conjCi ?raddfN /= ?Re_i ?Im_i ?Cl.
Qed.

(* T gate *)

Definition Tg : 
  'M[algC]_2 := (sqrtC 2%:R)^-1 *:'M{[::[::sqrtC 2%:R; 0]; [::0; 1 + 'i]]}.

Lemma T_unitary : Tg \is mxunitary.
Proof.
have [[Hs1 Hs2] Hs3] := (sqrtC2_neq0, sqrtC2_real, sqrtC2I_real).
apply/eqP/matrixP=> i j;
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) /= ?Cl //.
  by rewrite [_ * sqrtC _]mulrC divff // ?mul1r ?conjC1.
rewrite rmorphM (CrealP _) // mulrCA -mulrA.
rewrite -normCK -['i]mulr1 normC2_rect // expr1n.
rewrite mulrA -invfM -expr2 sqrtCK -mulr2n mulrC divff //.
by rewrite (eqC_nat _ 0).
Qed.

Lemma Tglift : 
  Mlift Tg = 
  (sqrtC 2%:R)^-1 *: 'M{[::[:: 1; -1; 0]; [:: 1; 1; 0]; [:: 0; 0; sqrtC 2%:R]]}.
Proof.
have [[Hs1 Hs2] Hs3] := (sqrtC2_neq0, sqrtC2_real, sqrtC2I_real).
apply/matrixP=> i j; 
 case/or3P : (i3E i) => /eqP->; case/or3P : (i3E j) => /eqP->;
  rewrite !mxE ?Cl //=.
- rewrite [_^-1 * _]mulrC divff // mul1r.
  rewrite Re_conj mulrC mulrDl mul1r.
  by rewrite Re_rect.
- rewrite [_^-1 * _]mulrC divff // mul1r.
  rewrite Im_conj mulrC mulrDl mul1r.
  by rewrite Im_rect.
- rewrite mulrC.
  rewrite [_^-1 * _]mulrC divff // conjC1 mul1r.
  by rewrite mulrC mulrDl mul1r Im_rect.
- rewrite mulrC.
  rewrite [_^-1 * _]mulrC divff // conjC1 mul1r.
  by rewrite mulrC mulrDl mul1r Re_rect.
by rewrite [_^-1 * _]mulrC divff // mul1r conjC1.
Qed.

(* w gate *)

Lemma sqrtC1i_norm : 
  (sqrtC 2%:R)^-1 * (1 + 'i) *  ((sqrtC 2%:R)^-1 * (1 + 'i))^* = 1%:R :> algC.
Proof.
have [[Hs1 Hs2] Hs3] := (sqrtC2_neq0, sqrtC2_real, sqrtC2I_real).
rewrite -normCK normrM exprMn.
rewrite -['i]mulr1 normC2_rect // expr1n.
rewrite normCK (CrealP _) //.
by rewrite  -invfM -expr2 sqrtCK -mulr2n mulrC divff // (eqC_nat _ 0).
Qed.

Definition W : 'M[algC]_2 := ((sqrtC 2%:R)^-1 * (1 + 'i))%:M.

Lemma W_unitary : W \is mxunitary.
Proof.
by apply/eqP/matrixP=> i j;
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) /= ?Cl // mulr1n ?sqrtC1i_norm //
           mulrC sqrtC1i_norm.
Qed.

Lemma Wlift : Mlift W = 1.
Proof.
by apply/matrixP=> i j; 
   case/or3P : (i3E i) => /eqP->; case/or3P : (i3E j) => /eqP->;
   rewrite !mxE ?Cl //= ?mulr1n ?sqrtC1i_norm 
                ?(Creal_ReP _ _) ?(Creal_ImP _ _).
Qed.

Lemma WW_i : W * W = 'i%:M.
Proof.
rewrite -[LHS]scalar_mxM.
rewrite mulrCA -mulrA -expr2 addrC sqrrD1 sqrCi.
rewrite -addrA addrC addrK mulrA -expr2 exprVn sqrtCK.
by rewrite mulrC -mulr_natr mulfK // (eqC_nat _ 0).
Qed.

Lemma HPxH_Pz : H^T* * Px * H = Pz.
Proof.
have [[Hs1 Hs2] Hs3] := (sqrtC2_neq0, sqrtC2_real, sqrtC2I_real).
by apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl //= (CrealP _) //
          -expr2 exprVn sqrtCK -1?[- _+ _]addrC ?subrr // -?opprD
           -mulr2n -[_ *+ 2]mulr_natl divff ?(eqC_nat _ 0).
Qed.

Lemma Mlift_Px : Mlift Px = 
  'M{[::[::1; 0; 0]; [::0; -1; 0];[::0; 0;-1]]}.
Proof.
by apply/matrixP=> i j; 
   case/or3P : (i3E i) => /eqP->; case/or3P : (i3E j) => /eqP->;
   rewrite !mxE ?Cl ?(Creal_ReP _ _) ?(Creal_ImP _ _) ?Cl.
Qed.

Lemma SPxS_i : H^T* * Px * H = Pz.
Proof.
have [[Hs1 Hs2] Hs3] := (sqrtC2_neq0, sqrtC2_real, sqrtC2I_real).
by apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl //= (CrealP _) //
          -expr2 exprVn sqrtCK -1?[- _+ _]addrC ?subrr // -?opprD
           -mulr2n -[_ *+ 2]mulr_natl divff ?(eqC_nat _ 0).
Qed.

(* Some relations *)

Lemma ST_com : S * Tg = Tg * S.
Proof.
by apply/matrixP=> i j; 
 case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
 rewrite !(s2E, mxE) !Cl //= mulrC.
Qed.

Lemma XT_com : 'P_0 * Tg = Tg * Px * S * W^T*.
Proof.
have [[Hs1 Hs2] Hs3] := (sqrtC2_neq0, sqrtC2_real, sqrtC2I_real).
apply/matrixP=> i j; 
 case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
 rewrite !(s2E, mxE) !Cl //=.
  rewrite -!mulrA; congr (_ * _).
  rewrite mulr1n rmorphM /= (CrealP _) //.
  rewrite mulrCA mulrC !mulrA divff // mul1r.
  rewrite -{2}['i]mulr1 conjC_rect // mulrBl.
  by rewrite mulr1 mul1r -expr2 sqrCi opprK addrC.
by rewrite mulr1n sqrtC1i_norm mulrC divff.
Qed.

Lemma WT_com : W * Tg = Tg * W.
Proof. by apply: sym_equal; exact: scalar_mxC. Qed.

Lemma TT_S : Tg * Tg = S.
Proof.
have [[Hs1 Hs2] Hs3] := (sqrtC2_neq0, sqrtC2_real, sqrtC2I_real).
apply/matrixP=> i j; 
 case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
 rewrite !(s2E, mxE) !Cl //=.
  by rewrite [_^-1 * _]mulrC divff // mul1r.
rewrite mulrCA !mulrA -mulrA.
rewrite -invfM mulrDl mul1r ['i * _]mulrDr mulr1 -!expr2 sqrtCK sqrCi.
rewrite addrC !addrA subrK -mulr2n -['i *+ 2]mulr_natl.
by rewrite mulrA  [_ * 2%:R]mulrC divff ?mul1r // (eqC_nat _ 0).
Qed.

Lemma H_invo : H * H = 1.
Proof.
have [[Hs1 Hs2] Hs3] := (sqrtC2_neq0, sqrtC2_real, sqrtC2I_real).
apply/matrixP=> i j; 
 case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
 rewrite !(s2E, mxE) !Cl ?subrr //=.
- by rewrite -invfM -expr2 sqrtCK -mulr2n -[_ *+ 2]mulr_natl divff // 
             (eqC_nat _ 0).
by rewrite -invfM -expr2 sqrtCK -mulr2n -[_ *+ 2]mulr_natl divff // 
           (eqC_nat _ 0).
Qed.

Lemma S_invoN : S * S = Pz.
Proof.
by apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl //= -expr2 sqrCi.
Qed.

Lemma SH_Px : S * H = (sqrtC 2%:R)^-1 *:'M{[::[::1; 1]; [::'i; -'i]]}.
Proof.
by apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl //= mulrC.
Qed.

Lemma HS_Px : H * S =  (sqrtC 2%:R)^-1 *:'M{[::[::1; 'i]; [::1; -'i]]}.
Proof.
apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl //=.
Qed.

Lemma H_PxPz : H = (sqrtC 2%:R)^-1 *: (Px + Pz).
Proof.
by apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl.
Qed.

Lemma S_IPz : S = (2%:R)^-1 *: (('i + 1)%:M - ('i - 1) *: Pz).
Proof.
apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl //=.
by rewrite addrC addrA subrK mulrC divff // (eqC_nat 2 0).
rewrite [_ + 1]addrC addrC !addrA subrK -mulr2n -['i *+ _]mulr_natl.
by rewrite mulrA [_ * _%:R]mulrC divff ?(eqC_nat 2 0) // mul1r.
Qed.

(*
Lemma HSH_Px : H * S * H = 1.
Proof.
apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl //=.
Qed.
*)

Lemma SPz_com : S * Pz = Pz * S.
Proof.
apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl //=.
Qed.

(*

Lemma HPz_com : H * Pz = Pz * H.
Proof.
apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl //=.
Qed.
*)

(*
Lemma HPz_com : S * H * Pz = 1.
Proof.
apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl //=.
Qed.
*)

Lemma SPzz_com : S * Pz = S^T*.
Proof.
by apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl //= conjCi.
Qed.

Lemma PzS_SV : Pz * S = S^T*.
Proof.
by apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl //= conjCi.
Qed.

Lemma SPz_SV : S * Pz = S^T*.
Proof.
by apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl //= conjCi.
Qed.

Lemma PzS_SVx : Pz * S = S^T*.
Proof.
by apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl //= conjCi.
Qed.

(*
Lemma HPz_SV : H * S * S = 1.
Proof.
 apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl //=.
Qed.
*)

(*
Lemma PzS_SVy : H * S * S = 1.
Proof.
by apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl //= conjCi.
Qed.
*)

(*
Lemma SHS : S * H * S = 1.
Proof.
apply/matrixP=> i j; 
   case/orP : (i2E i) => /eqP->; case/orP : (i2E j) => /eqP->;
   rewrite !(s2E, mxE) !Cl //=.
Qed.
*)

End M.

 

