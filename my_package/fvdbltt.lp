symbol Prop : TYPE;
symbol Prf : Prop → TYPE;
builtin "Prop" ≔ Prop;
builtin "P" ≔ Prf;

symbol Cat : TYPE;

inductive CatCtx : TYPE ≔ empty : CatCtx
    | concat : CatCtx → Cat → CatCtx;

symbol ⨉ : Cat → Cat → Cat;

notation ⨉ infix left 7;

symbol 1 : Cat;

symbol Func : CatCtx → Cat → TYPE;

symbol pair [Γ : CatCtx] [I J : Cat] : Func Γ I → Func Γ J → Func Γ (I ⨉ J);

symbol pr_0 [Γ : CatCtx] [I J : Cat] : Func Γ (I ⨉ J) → Func Γ I;

symbol pr_1 [Γ : CatCtx] [I J : Cat] : Func Γ (I ⨉ J) → Func Γ J;

symbol ǃ [Γ : CatCtx] : Func Γ 1;

inductive FuncSeq : CatCtx → CatCtx → TYPE ≔ 
    emptySeq [Γ : CatCtx] : FuncSeq Γ empty
    | concatSeq [Γ Δ : CatCtx] [I : Cat] : FuncSeq Γ Δ → Func Γ I → FuncSeq Γ (concat Δ I); 

print pair;

rule $s ↪ ǃ;
