import Mathlib.CategoryTheory.Category.Cat

/-!
# Categories, Chapter 1: Introduction

The introductory paragraph is motivational and historical.  Its precise
category-theoretic content is represented here by Mathlib's universe-indexed
category `Cat`, which already carries the bicategory structure whose
1-morphisms are functors and whose 2-morphisms are natural transformations.
The textbook's proper-class wording is therefore represented at each fixed
pair of object and morphism universes.
-/

universe v u

namespace LastLib.BookCategories.Chapter01

/-- At fixed universes, the category of categories is a bicategory. -/
@[instance_reducible]
def categoryOfCategoriesBicategory :
    CategoryTheory.Bicategory (CategoryTheory.Cat.{v, u}) :=
  CategoryTheory.Cat.bicategory

end LastLib.BookCategories.Chapter01
