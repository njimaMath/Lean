import Mathlib
namespace Foo
lemma Foo.bar : True := by
  trivial
#check Foo.bar
#check Foo.Foo.bar
end Foo
