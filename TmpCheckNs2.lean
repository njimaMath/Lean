import Mathlib
namespace Foo
lemma Foo.bar : True := by
  trivial
end Foo
#check Foo.bar
#check Foo.Foo.bar
