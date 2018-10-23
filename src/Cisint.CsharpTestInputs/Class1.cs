using System;
using System.Collections.Generic;
using System.Linq;

namespace Cisint.CsharpTestInputs
{
    public interface IWriter
    {
        void AddAttribute(string name, string value);
        void BeginTag(string name);
        void EndTag();
    }

    public class PropertyDescriptor
    {
        public PropertyDescriptor(object defaultValue)
        {
            DefaultValue = defaultValue;
        }

        public object DefaultValue { get; }

        public static PropertyDescriptor Register<T>(string name, T defaultValue = default(T))
        {
            Console.WriteLine($"Registering property {name}");
            return new PropertyDescriptor(defaultValue);
        }
    }

    public class SomethingLikeControl
    {
        private Dictionary<PropertyDescriptor, object> properties = new Dictionary<PropertyDescriptor, object>();
        public T GetValue<T>(PropertyDescriptor property) => properties.TryGetValue(property, out var result) ? (T)result : (T)property.DefaultValue;

        public void SetValue(PropertyDescriptor property, object value) => properties[property] = value;

        public virtual void Render(IWriter writer)
        {
        }
    }

    public class MaybeHtmlControl: SomethingLikeControl
    {
        public static readonly PropertyDescriptor MagicProperty = PropertyDescriptor.Register<string>("Id");
        public static readonly PropertyDescriptor TagNameProperty = PropertyDescriptor.Register<string>("TagName", defaultValue: "span");
        public Dictionary<string, object> Attributes { get; } = new Dictionary<string, object>();

        public override void Render(IWriter writer)
        {
            if (this.GetValue<string>(MagicProperty) is string magicValue)
            {
                writer.AddAttribute("id", magicValue);
            }

            foreach(var a in Attributes.AsEnumerable())
            {
                writer.AddAttribute(a.Key, a.Value.ToString());
            }

            writer.BeginTag(this.GetValue<string>(TagNameProperty));
            writer.EndTag();
        }
    }


    public class Class1
    {
        public static void PlayWithSomeControl(IWriter writer, int mode)
        {
            var c = new MaybeHtmlControl() {
                Attributes = { ["a"] = "kokos" }
            };
            if ((mode & 1) != 0)
                c.Attributes.Add("class", "css-class-123");
            if ((mode & 2) != 0)
                c.SetValue(MaybeHtmlControl.MagicProperty, "id123");
            if ((mode & 4) != 0)
                c.SetValue(MaybeHtmlControl.TagNameProperty, "div");

            c.Render(writer);
        }

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
