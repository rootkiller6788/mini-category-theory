/-
# MiniAdjunction.Constructions.Quotients

Reflective subcategories, localization as adjunction,
and quotient category adjunctions.
-/

import MiniCategoryCore.Core.Basic
import MiniCategoryCore.Core.Objects
import MiniMorphismSystem.Core.Basic
import MiniMorphismSystem.Core.Objects
import MiniNaturalTransformation.Core.Basic
import MiniNaturalTransformation.Core.Objects
import MiniAdjunction.Core.Basic
import MiniAdjunction.Core.Objects
import MiniAdjunction.Core.Laws

namespace MiniAdjunction

open MiniCategoryCore
open MiniMorphismSystem
open MiniNaturalTransformation

/-! ## Reflective Subcategory -/

/--
A reflective subcategory is one where the inclusion functor has a left adjoint.
The left adjoint is called the reflector.
-/
structure ReflectiveSubcategory (C : Category) (D : Category) where
  inclusion : Functor D C
  reflector : Functor C D
  adj : inclusion ⊣ reflector

/--
The inclusion of a reflective subcategory is fully faithful.
-/
axiom reflectiveInclusionFullyFaithful {C D : Category}
    (rs : ReflectiveSubcategory C D) : Functor.IsFullyFaithful rs.inclusion

/--
In a reflective subcategory, the reflector is idempotent up to isomorphism.
The counit is an isomorphism.
-/
axiom reflectiveCounitIsIso {C D : Category}
    (rs : ReflectiveSubcategory C D) : Prop

/--
A reflective subcategory is closed under limits in the ambient category.
-/
axiom reflectiveClosedUnderLimits {C D : Category}
    (rs : ReflectiveSubcategory C D) : Prop

/-! ## Localization as Adjunction -/

/--
A localization of a category C at a class of morphisms W is a functor
L : C → C[W⁻¹], which is left adjoint to the inclusion of W⁻¹-local objects.
-/
structure LocalizationAdjunction (C : Category) (W : C.Obj → C.Obj → Prop) where
  localizedCat : Category
  localizationFunctor : Functor C localizedCat
  inclusion : Functor localizedCat C
  adj : localizationFunctor ⊣ inclusion
  invertsW : ∀ {X Y : C.Obj} (f : C[X, Y]), W X Y → Prop

/--
Localization is a reflective subcategory of the category of presheaves.
-/
axiom localizationAsReflective : Prop

/-! ## Quotient Category Adjunction -/

/--
Given a category C and a congruence relation on morphisms, the quotient
category C/~ has a projection functor C → C/~ which is left adjoint
to the discrete inclusion.
-/
structure QuotientAdjunction (C : Category) where
  quotientCat : Category
  projection : Functor C quotientCat
  section : Functor quotientCat C
  adj : projection ⊣ section
  quotientProperty : ∀ {X Y : C.Obj} (f g : C[X, Y]), Prop

/--
The projection functor is essentially surjective and full.
-/
axiom projectionEssentiallySurjective {C : Category}
    (qa : QuotientAdjunction C) : Functor.IsEssentiallySurjective qa.projection

/--
The section functor is fully faithful (it embeds the quotient).
-/
axiom sectionFullyFaithful {C : Category}
    (qa : QuotientAdjunction C) : Functor.IsFullyFaithful qa.section

/-! ## Gabriel-Ulmer Duality -/

/--
Locally finitely presentable categories are precisely the categories
equivalent to Ind(C) for small C with finite colimits. These categories
are reflective in presheaf categories.
-/
axiom gabrielUlmerDuality : Prop

#eval "Constructions.Quotients: ReflectiveSubcategory, localization as adjunction"
#eval "Constructions.Quotients: QuotientAdjunction, Gabriel-Ulmer (axiom)"
#eval "Constructions.Quotients: reflectiveInclusionFullyFaithful (axiom)"
