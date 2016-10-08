{-# OPTIONS --no-eta --without-K --rewriting #-}

module SetoidSimple.Norm.Model where

open import Level
open import lib

open import SetoidSimple.Derived
open import SetoidSimple.Syntax
open import SetoidSimple.Elim

open import SetoidSimple.Norm.Methods1
open import SetoidSimple.Norm.Methods2
open import SetoidSimple.Norm.Methods3
open import SetoidSimple.Norm.Methods4

private
  postulate cheat : ∀ {α}{A : Set α} → A

M : DModel {suc zero}{zero}
M = record
      { Tyᴹ    = Tyᴹ
      ; Conᴹ   = Conᴹ
      ; Tmsᴹ   = Tmsᴹ
      ; Tmᴹ    = Tmᴹ

      ; ιᴹ     = ιᴹ
      ; _⇒ᴹ_   = _⇒ᴹ_

      ; ∙ᴹ     = ∙ᴹ
      ; _,ᴹ_   = _,ᴹ_

      ; idᴹ    = idᴹ

      ; _∘ᴹ_   = λ {a}{b}{c}{d}{e}{f} → _∘ᴹ_ {a}{b}{c}{d}{e}{f}

      ; εᴹ     = εᴹ

      ; _,ₛᴹ_  = λ {a}{b}{c}{d}{e} → _,ₛᴹ_ {a}{b}{c}{d}{e}

      ; π₁ᴹ    = λ {a}{b}{c}{d}{e}{f} → π₁ᴹ {a}{b}{c}{d}{e}{f}

      ; _[_]ᴹ  = λ {a}{b}{c}{d}{e}{f} → _[_]ᴹ {a}{b}{c}{d}{e}{f}

      ; π₂ᴹ    = λ {a}{b}{c}{d}{e}{f} → π₂ᴹ {a}{b}{c}{d}{e}{f}

      ; [id]ᴹ  = [id]ᴹ

      ; [][]ᴹ  = λ {a}{b}{c}{d}{e}{f}{g}{h}{i}{j}{k}{l}{m}{n}
                 → [][]ᴹ {a}{b}{c}{d}{e}{f}{g}{h}{i}{j}{k}{l}{m}{n}

      ; idlᴹ   = λ {a}{b}{c}{d}{e}{f} → idlᴹ {a}{b}{c}{d}{e}{f}

      ; idrᴹ   = λ {a}{b}{c}{d}{e}{f} → idrᴹ {a}{b}{c}{d}{e}{f}

      ; assᴹ   = λ {a}{b}{c}{d}{e}{f}{g}{h}{i}{j}{k}{l}{m}{n}
                 → assᴹ {a}{b}{c}{d}{e}{f}{g}{h}{i}{j}{k}{l}{m}{n}

      ; ,∘ᴹ    = λ {a}{b}{c}{d}{e}{f}{g}{h}{i}{j}{k}{l}{m}{n}
                 → ,∘ᴹ {a}{b}{c}{d}{e}{f}{g}{h}{i}{j}{k}{l}{m}{n}

      ; ,β₁ᴹ   = λ {a}{b}{c}{d}{e}{f}{g}{h}{i}{j}
                 → ,β₁ᴹ {a}{b}{c}{d}{e}{f}{g}{h}{i}{j}

      ; ,ηᴹ    = λ {a}{b}{c}{d}{e}{f}{g}{h} → ,ηᴹ {a}{b}{c}{d}{e}{f}{g}{h}

      ; ∙ηᴹ    = refl

      ; ,β₂ᴹ   = λ {a}{b}{c}{d}{e}{f}{g}{h} → ,β₂ᴹ {a}{b}{c}{d}{e}{f}{g}{h}

      ; lamᴹ   = λ {a}{b}{c}{d}{e}{f}{g} → lamᴹ {a}{b}{c}{d}{e}{f}{g}

      ; appᴹ   = λ {a}{b}{c}{d}{e}{f}{g} → appᴹ {a}{b}{c}{d}{e}{f}{g}

      ; lam[]ᴹ = cheat
      ; ⇒βᴹ    = cheat
      ; ⇒ηᴹ    = cheat
      }
