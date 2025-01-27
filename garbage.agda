    -- We need some calculation here for the formalization

    altogether-ι′ : ∀ {Γ♪} → alltogether (ι′ Γ♪) ≡ Γ♪
    altogether-ι′ {ι Γ} = ≡refl
    altogether-ι′ {Γ♪ ⨾ Δ} = 
        begin 
            alltogether (ι′ (Γ♪ ⨾ Δ))
        ≡⟨ (≡refl) ⟩
            alltogether (ιpre (head (Γ♪ ⨾ Δ)) ⨾pre (Γ♪ ⨾ Δ) , ≡refl , ≡refl)
        ≡⟨ ≡refl ⟩
            alltogether (ιpre (head (Γ♪ ⨾ Δ)) ⨾pre (Γ♪) , ≡refl , ≡refl) ⨾ Δ
        ≡⟨ ≡refl ⟩
            alltogether (ι′ (Γ♪)) ⨾ Δ
        ≡⟨ cong ( λ θ → θ ⨾ Δ) altogether-ι′ ⟩
            Γ♪ ⨾ Δ
        ∎

    alt-ιpre-head-⨾pre : ∀ {Γ♪} → alltogether ( ( ιpre ( head Γ♪) ⨾pre Γ♪) , ≡refl , ≡refl) ≡ Γ♪
    alt-ιpre-head-⨾pre {ι x} = ≡refl
    alt-ιpre-head-⨾pre {Γ♪ ⨾ Δ} = 
        begin 
            alltogether ( ( ιpre ( head (Γ♪ ⨾ Δ)) ⨾pre (Γ♪ ⨾ Δ)) , ≡refl , ≡refl)
        ≡⟨ ≡refl ⟩
            alltogether ( ( ιpre ( head Γ♪) ⨾pre (Γ♪ ⨾ Δ)) , ≡refl , ≡refl)
        ≡⟨ ≡refl ⟩
            alltogether ( ( ιpre ( head Γ♪) ⨾pre Γ♪) , ≡refl , ≡refl) ⨾ Δ
        ≡⟨ {!   !} ⟩
            Γ♪ ⨾ Δ
        ∎
        
    alltogether-⨾ : ∀ { Γ♩ Δ } → ( alltogether (Γ♩ ⨾′ ι Δ)) ≡ ( alltogether Γ♩ )
    alltogether-⨾ {Γ♩} {Δ} = ≡refl

    alltogether-⨾- : ∀ { Γ♩ Δ♪ } → ( alltogether Γ♩ ⨾- Δ♪ ) ≡ ( alltogether ( Γ♩ ⨾′ Δ♪ ))
    alltogether-⨾- {Γ♩} {ι Δ} = 
        begin
            alltogether Γ♩ ⨾- ι Δ
        ≡⟨ {!   !} ⟩
            alltogether Γ♩ 
        ≡⟨ sym (alltogether-⨾ {Γ♩} {Δ})  ⟩
            alltogether ( Γ♩ ⨾′ ι Δ )
        ∎
    alltogether-⨾- {Γ♩} {Δ♪ ⨾ x} = {!   !}
    -- 