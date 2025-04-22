axiom A₀ : Type
axiom A₁ : Type
axiom A₂ : Id Type A₀ A₁

synth A₂ .trr.1
synth A₂ .trl.1
synth A₂ .liftr.1
synth A₂ .liftl.1

axiom a₀ : A₀
synth A₂ .trr.1 a₀
synth A₂ .liftr.1 a₀

axiom a₁ : A₁
synth A₂ .trl.1 a₁
synth A₂ .liftl.1 a₁
