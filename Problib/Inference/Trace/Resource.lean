namespace Problib.Inference.Trace

universe u v

/-- Ordered, grade-indexed composition whose domain is carried by a proof. -/
structure Resource (Grade : Type u) (Carrier : Grade → Type v) where
  Compatible : Grade → Grade → Prop
  appendGrade : {left right : Grade} → Compatible left right → Grade
  append : {left right : Grade} →
    (compatible : Compatible left right) →
      Carrier left → Carrier right → Carrier (appendGrade compatible)

/-- A checked composition is lossless when its witness also determines a split. -/
structure Lossless {Grade : Type u} {Carrier : Grade → Type v}
    (resource : Resource Grade Carrier) where
  split : {left right : Grade} →
    (compatible : resource.Compatible left right) →
      Carrier (resource.appendGrade compatible) →
        Carrier left × Carrier right
  split_append : ∀ {left right : Grade}
    (compatible : resource.Compatible left right)
    (leftValue : Carrier left) (rightValue : Carrier right),
    split compatible (resource.append compatible leftValue rightValue) =
      (leftValue, rightValue)
  append_split : ∀ {left right : Grade}
    (compatible : resource.Compatible left right)
    (value : Carrier (resource.appendGrade compatible)),
    resource.append compatible
        (split compatible value).1 (split compatible value).2 = value

def Resource.Collision {Grade : Type u} {Carrier : Grade → Type v}
    (resource : Resource Grade Carrier) (left right : Grade) : Prop :=
  ¬resource.Compatible left right

end Problib.Inference.Trace
