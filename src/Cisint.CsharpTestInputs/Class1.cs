using System;
using System.Collections.Generic;

namespace Cisint.CsharpTestInputs
{
    public class Class1
    {
        public static IEnumerable<int> YieldSomeInts(int max)
        {
            yield return -100;
            for (int i = 0; i < max; i++)
            {
                yield return i;
            }
        }
    }
}
