using System;

namespace Cisint.DynamicEvaluator
{
    public static class Evaluator
    {
        public static dynamic Add(dynamic a, dynamic b) => a + b;
        public static dynamic And(dynamic a, dynamic b) => a & b;
        public static bool Eq(dynamic a, dynamic b) => a == b;
        public static bool GreaterThan(dynamic a, dynamic b) => a > b;
        public static bool LessThan(dynamic a, dynamic b) => a < b;
        public static T ConvertTo<T>(dynamic a) => unchecked((T)a);
        public static T ConvertToChecked<T>(dynamic a) => checked((T)a);
        public static dynamic Divide(dynamic a, dynamic b) => a / b;
        public static dynamic Multiply(dynamic a, dynamic b) => a * b;
        public static dynamic Negate(dynamic a) => -a;
        public static dynamic BitNot(dynamic a) => ~a;
        public static dynamic Or(dynamic a, dynamic b) => a | b;
        public static dynamic Rem(dynamic a, dynamic b) => a % b;
        public static dynamic Shr(dynamic a, dynamic b) => a >> b;
        public static dynamic Shl(dynamic a, dynamic b) => a << b;
        public static dynamic Sub(dynamic a, dynamic b) => a - b;
        public static dynamic Xor(dynamic a, dynamic b) => a ^ b;
    }
}
