using System;
using System.Collections;
using System.Collections.Generic;

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

        public static T GetDefault<T>() => default(T);
    }

    public class X<K, V> : IDictionary<K, V>
    {
        public V this[K key] { get => throw new NotImplementedException(); set => throw new NotImplementedException(); }

        public ICollection<K> Keys => throw new NotImplementedException();

        public ICollection<V> Values => throw new NotImplementedException();

        public int Count => throw new NotImplementedException();

        public bool IsReadOnly => throw new NotImplementedException();

        public void Add(K key, V value)
        {
            throw new NotImplementedException();
        }

        public void Add(KeyValuePair<K, V> item)
        {
            throw new NotImplementedException();
        }

        public void Clear()
        {
            throw new NotImplementedException();
        }

        public bool Contains(KeyValuePair<K, V> item)
        {
            throw new NotImplementedException();
        }

        public bool ContainsKey(K key)
        {
            throw new NotImplementedException();
        }

        public void CopyTo(KeyValuePair<K, V>[] array, int arrayIndex)
        {
            throw new NotImplementedException();
        }

        public IEnumerator<KeyValuePair<K, V>> GetEnumerator()
        {
            throw new NotImplementedException();
        }

        public bool Remove(K key)
        {
            throw new NotImplementedException();
        }

        public bool Remove(KeyValuePair<K, V> item)
        {
            throw new NotImplementedException();
        }

        public bool TryGetValue(K key, out V value)
        {
            throw new NotImplementedException();
        }

        IEnumerator IEnumerable.GetEnumerator()
        {
            throw new NotImplementedException();
        }
    }
}
