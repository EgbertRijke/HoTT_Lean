open sigma eq

namespace graphs
-- We begin by defining the fundamental structure of the graph model

-- The context in the graph model are the graphs themselves
structure ctx :=
  ( vertex : Type)
  ( edge : vertex → vertex → Type)

-- The families in the graph model are families of graphs
structure fam (G : ctx) :=
  ( vertex : ctx.vertex G → Type)
  ( edge : Π{i j : ctx.vertex G}, ctx.edge G i j → vertex i → vertex j → Type)

-- Global terms of families are matching families of terms
structure tm {G : ctx} (A : fam G) :=
  ( vertex : Π(i : ctx.vertex G), fam.vertex A i)
  ( edge : Π{i j : ctx.vertex G}, Π(e : ctx.edge G i j), fam.edge A e (vertex i) (vertex j))

section extension
-- The graph model is an extension algebra

variable {G : ctx}

-- Extension in the graph model is interpetred using Sigma (by lack of something better)
definition ctxext (A : fam G) : ctx :=
  ctx.mk
    ( Σ (i : ctx.vertex G), fam.vertex A i)
    ( λ p q,
        Σ (e : ctx.edge G (pr1 p) (pr1 q)),
          fam.edge A e (pr2 p) (pr2 q))

-- There is also family extension, which turns out to be equivalent to the dependent
-- pair graph
definition famext (A : fam G) (P : fam (ctxext A)) : fam G :=
  fam.mk
    ( λ i, Σ (x : fam.vertex A i), fam.vertex P ⟨i,x⟩)
    ( λ i j e p q,
        Σ (f : fam.edge A e (pr1 p) (pr1 q)),
          fam.edge P ⟨e,f⟩ (pr2 p) (pr2 q))

end extension

namespace wk
-- The graph model is a weakening algebra

variable {G : ctx}
variable (A : fam G)

definition ctx (B : fam G) : fam (ctxext A) :=
  fam.mk
    ( λ p, fam.vertex B (pr1 p))
    ( λ p q e, fam.edge B (pr1 e))

variable {B : fam G}

definition fam (Q : fam (ctxext B)) : fam (ctxext (wk.ctx A B)) :=
  fam.mk
    ( λ p, fam.vertex Q ⟨pr1 (pr1 p),pr2 p⟩)
    ( λ p q e, fam.edge Q ⟨(pr1 (pr1 e)),pr2 e⟩)

variable {Q : graphs.fam (ctxext B)}

definition tm (g : graphs.tm Q) : tm (wk.fam A Q) :=
  tm.mk
    ( λ p, tm.vertex g (⟨pr1 (pr1 p),pr2 p⟩))
    ( λ p q e, tm.edge g (⟨pr1 (pr1 e),pr2 e⟩))

end wk

namespace proj
-- The graph model is a projection algebra

variables {G : ctx} {A : fam G}

definition idm : tm (wk.ctx A A) :=
  tm.mk
    ( λ p, pr2 p)
    ( λ p q e, pr2 e)

end proj

namespace subst
-- The graph model is a substitution algebra

variables {G : ctx} {A : fam G} (x : tm A)

definition ctx (P : fam (ctxext A)) : fam G :=
  fam.mk
    ( λ i, fam.vertex P ⟨i, tm.vertex x i⟩)
    ( λ i j e, fam.edge P ⟨e, tm.edge x e⟩)

definition fam {P : fam (ctxext A)} (Q : fam (ctxext P)) : fam (ctxext (subst.ctx x P)) :=
  fam.mk
    ( λ p, fam.vertex Q ⟨⟨pr1 p, tm.vertex x (pr1 p)⟩, pr2 p⟩)
    ( λ p q e, fam.edge Q ⟨⟨pr1 e, tm.edge x (pr1 e)⟩, pr2 e⟩)

definition tm {P : graphs.fam (ctxext A)} {Q : graphs.fam (ctxext P)} (g : tm Q) : tm (subst.fam x Q) :=
  tm.mk
    ( λ p, tm.vertex g ⟨⟨pr1 p, tm.vertex x (pr1 p)⟩, pr2 p⟩)
    ( λ p q e, tm.edge g ⟨⟨pr1 e, tm.edge x (pr1 e)⟩, pr2 e⟩)

end subst

section Types_as_graphs
-- Types as graphs.

definition Delta (A : Type) : ctx :=
  ctx.mk A (λ x y, x = y)

end Types_as_graphs

end graphs
