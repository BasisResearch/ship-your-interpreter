import Vsa.While.Derive
import Vsa.While.Programs

namespace Vsa.While.Validation

open Vsa.While Vsa.While.Programs

set_option maxRecDepth 4000000

theorem whileWl_valid : BigStep whileWl "55\n2500\n36\n" := by
  bigstep_derive

theorem arithmetic_valid : BigStep arithmeticWl
    "7\n9\n3\n1\n-2\n26\n1000000000000\n4\nfalse true false\ntrue true false true\ntrue true true false\nfalse true true false\n" := by
  bigstep_derive

theorem for_valid : BigStep forWl
    "1\n2\nFizz\n4\nBuzz\nFizz\n7\n8\nFizz\nBuzz\n11\nFizz\n13\n14\nFizzBuzz\n5050\n37\n3\n01234\n" := by
  bigstep_derive

theorem scope_valid : BigStep scopeWl "2\n3\n1\n20\n14 5\n3\nasserts ok\n" := by
  bigstep_derive

theorem strings_valid : BigStep stringsWl
    "hello world\nvalue: 42\n12\ntrue true\ntrue true\nline1\nline2\ntab\there\nquote: \"hi\"\n" := by
  bigstep_derive

end Vsa.While.Validation
