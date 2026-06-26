import MiniYonedaLite

open MiniYonedaLite
open MiniCategoryCore
open MiniFunctorCore
open MiniNaturalTransformation

-- Regression checks: verify all key definitions are accessible
#check isRepresentable
#check presheafCategory
#check isRepresentablePresheaf
#check yonedaEmbedding
#check yonedaAsFunctor
#check inYonedaImage
#check yonedaLemma
#check yonedaIsFullyFaithful
#check representingObjectUnique
#check yonedaLemmaAxiom
#check yonedaEmbeddingFullyFaithful
#check yonedaEmbeddingIsEmbedding
#check yonedaLemmaFromEmbedding
