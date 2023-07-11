Require Export CompLat.

Record bilattice := {
  base :> Type;

  meett : base -> base -> base;
  joint : base -> base -> base;
  meetCt : forall a b, meett a b = meett b a;
  joinCt : forall a b, joint a b = joint b a;
  meetAt : forall a b c, meett a (meett b c) = meett (meett a b) c;
  joinAt : forall a b c, joint a (joint b c) = joint (joint a b) c;
  joinKt : forall a b, meett a (joint a b) = a;
  meetKt : forall a b, joint a (meett a b) = a;

  meetk : base -> base -> base;
  joink : base -> base -> base;
  meetCk : forall a b, meetk a b = meetk b a;
  joinCk : forall a b, joink a b = joink b a;
  meetAk : forall a b c, meetk a (meetk b c) = meetk (meetk a b) c;
  joinAk : forall a b c, joink a (joink b c) = joink (joink a b) c;
  joinKk : forall a b, meetk a (joink a b) = a;
  meetKk : forall a b, joink a (meetk a b) = a;
}.

Definition latticet (L : bilattice) : lattice := {|
  meetC := meetCt L;
  joinC := joinCt L;
  meetA := meetAt L;
  joinA := joinAt L;
  joinK := joinKt L;
  meetK := meetKt L;
|}.

Definition latticek (L : bilattice) : lattice := {|
  meetC := meetCk L;
  joinC := joinCk L;
  meetA := meetAk L;
  joinA := joinAk L;
  joinK := joinKk L;
  meetK := meetKk L;
|}.

Record bicomplattice := {
  blat : bilattice;

  latt := latticet blat;  
  supt : Ensemble latt -> latt;
  inft : Ensemble latt -> latt;
  is_upbt : forall (A : Ensemble latt) a, a \in A -> a ≺ (supt A);
  is_supt : forall (A : Ensemble latt) a,
           (forall b, b \in A -> b ≺ a) -> (supt A) ≺ a;
  is_lowbt : forall (A : Ensemble latt) a, a \in A -> (inft A) ≺ a;
  is_inft : forall (A : Ensemble latt) a,
           (forall b, b \in A -> a ≺ b) -> a ≺ (inft A);
  bott := inft (Full_set latt);
  topt := supt (Full_set latt);

  latk := latticet blat;  
  supk : Ensemble latk -> latk;
  infk : Ensemble latk -> latk;
  is_upbk : forall (A : Ensemble latk) a, a \in A -> a ≺ (supk A);
  is_supk : forall (A : Ensemble latk) a,
           (forall b, b \in A -> b ≺ a) -> (supk A) ≺ a;
  is_lowbk : forall (A : Ensemble latk) a, a \in A -> (infk A) ≺ a;
  is_infk : forall (A : Ensemble latk) a,
           (forall b, b \in A -> a ≺ b) -> a ≺ (infk A);
  botk := infk (Full_set latk);
  topk := supk (Full_set latk);

}.

Definition complatt (L : bicomplattice) := {|
  is_upb := is_upbt L;
  is_sup := is_supt L;
  is_lowb := is_lowbt L;
  is_inf := is_inft L;
|}.

Definition complatk (L : bicomplattice) := {|
  is_upb := is_upbk L;
  is_sup := is_supk L;
  is_lowb := is_lowbk L;
  is_inf := is_infk L;
|}.

