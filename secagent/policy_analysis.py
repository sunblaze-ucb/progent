#!/usr/bin/env python3
from z3 import *
from .role_analyzer import regex_to_z3_expr_search
import os
import sys

# Define a global Z3 datatype for null.
NullType = Datatype('NullType')
NullType.declare('null')
NullType = NullType.create()

# Define a Z3 datatype for arrays.
# ArrayWrapper has two fields:
#   a: an array from Int to Type
#   len: an integer representing the length of the array.

# Array wrapper for arrays of strings.
ArrayWrapper_string = Datatype('ArrayWrapper_string')
ArrayWrapper_string.declare('mkArrayWrapper', ('a', ArraySort(IntSort(), StringSort())), ('len', IntSort()))
ArrayWrapper_string = ArrayWrapper_string.create()

# Array wrapper for arrays of integers.
ArrayWrapper_integer = Datatype('ArrayWrapper_integer')
ArrayWrapper_integer.declare('mkArrayWrapper', ('a', ArraySort(IntSort(), IntSort())), ('len', IntSort()))
ArrayWrapper_integer = ArrayWrapper_integer.create()

# Array wrapper for arrays of reals (numbers).
ArrayWrapper_number = Datatype('ArrayWrapper_number')
ArrayWrapper_number.declare('mkArrayWrapper', ('a', ArraySort(IntSort(), RealSort())), ('len', IntSort()))
ArrayWrapper_number = ArrayWrapper_number.create()

# Array wrapper for arrays of booleans.
ArrayWrapper_boolean = Datatype('ArrayWrapper_boolean')
ArrayWrapper_boolean.declare('mkArrayWrapper', ('a', ArraySort(IntSort(), BoolSort())), ('len', IntSort()))
ArrayWrapper_boolean = ArrayWrapper_boolean.create()

# Array wrapper for arrays of null.
ArrayWrapper_null = Datatype('ArrayWrapper_null')
ArrayWrapper_null.declare('mkArrayWrapper', ('a', ArraySort(IntSort(), NullType)), ('len', IntSort()))
ArrayWrapper_null = ArrayWrapper_null.create()

# A list of all array wrappers.
ARRAY_WRAPPERS = [ArrayWrapper_string, ArrayWrapper_integer, ArrayWrapper_number, ArrayWrapper_boolean, ArrayWrapper_null]

# Map each array wrapper sort to its accessors (the 'a' field and the 'len' field).
ARRAY_WRAPPER_ACCESSORS = {
    ArrayWrapper_string: (ArrayWrapper_string.a, ArrayWrapper_string.len),
    ArrayWrapper_integer: (ArrayWrapper_integer.a, ArrayWrapper_integer.len),
    ArrayWrapper_number: (ArrayWrapper_number.a, ArrayWrapper_number.len),
    ArrayWrapper_boolean: (ArrayWrapper_boolean.a, ArrayWrapper_boolean.len),
    ArrayWrapper_null: (ArrayWrapper_null.a, ArrayWrapper_null.len)
}


# JSON objects are not modelled beyond their type: a value of this sort stands
# for "some object". Only used when search_all_types() is on.
JsonObject = DeclareSort('JsonObject')


def search_all_types():
    """
    Whether the subset check looks for a counter example among values of every
    type (see the limitations listed on security_policy_subset_check).
    """
    return os.getenv("SECAGENT_SUBSET_CHECK_ALL_TYPES", "False").lower() == "true"


# Keywords build_constraints translates. Any other keyword is refused, because
# jsonschema may enforce it at runtime and ignoring it would read a restriction
# as no restriction.
SUPPORTED_KEYWORDS = {
    "enum", "const", "anyOf", "allOf", "oneOf", "not", "if", "then", "else", "type",
    "pattern", "minLength", "maxLength",
    "multipleOf", "minimum", "exclusiveMinimum", "maximum", "exclusiveMaximum",
    "items", "minItems", "maxItems",
}
# Keywords that never reject a value ("format" is not asserted by jsonschema.validate).
ANNOTATION_KEYWORDS = {"title", "description", "default", "examples", "format", "$comment", "deprecated", "readOnly", "writeOnly"}

ARRAY_WRAPPER_ELEMENT_SORTS = {
    ArrayWrapper_string: StringSort(),
    ArrayWrapper_integer: IntSort(),
    ArrayWrapper_number: RealSort(),
    ArrayWrapper_boolean: BoolSort(),
    ArrayWrapper_null: NullType,
}


def scalar_to_z3(sort, value):
    """
    Return the Z3 term of the given sort for a JSON scalar, or None if the value
    is not of that sort. A number with an integral value is both an integer and a number.
    """
    if isinstance(value, bool):
        return BoolVal(value) if sort == BoolSort() else None
    if isinstance(value, str):
        return StringVal(value) if sort == StringSort() else None
    if isinstance(value, int):
        if sort == IntSort():
            return IntVal(value)
        return RealVal(value) if sort == RealSort() else None
    if isinstance(value, float):
        if sort == RealSort():
            return RealVal(value)
        return IntVal(int(value)) if sort == IntSort() and value.is_integer() else None
    if value is None:
        return NullType.null if sort == NullType else None
    raise NotImplementedError(f"ERROR: value {value!r} not implemented")


def value_to_z3(sort, value):
    """
    Return the Z3 term of the given sort for a JSON value, or None if the value
    is not of that sort.
    """
    if isinstance(value, dict):
        raise NotImplementedError(f"ERROR: object value {value!r} not implemented")
    if isinstance(value, list):
        if sort not in ARRAY_WRAPPERS:
            return None
        elements = [scalar_to_z3(ARRAY_WRAPPER_ELEMENT_SORTS[sort], e) for e in value]
        if any(e is None for e in elements):
            return None
        # var.sort() does not carry the constructor, so use the declared wrapper.
        wrapper = next(aw for aw in ARRAY_WRAPPERS if aw == sort)
        arr_term = make_array_from_list([], wrapper)
        for i, e in enumerate(elements):
            arr_term = Store(arr_term, i, e)
        return wrapper.mkArrayWrapper(arr_term, len(value))
    if sort in ARRAY_WRAPPERS or sort == JsonObject:
        return None
    return scalar_to_z3(sort, value)


def json_type_name(value):
    """
    Return the JSON Schema type name of a JSON value.
    """
    if isinstance(value, bool):
        return "boolean"
    if isinstance(value, str):
        return "string"
    if isinstance(value, int):
        return "integer"
    if isinstance(value, float):
        return "number"
    if value is None:
        return "null"
    if isinstance(value, list):
        return "array"
    return "object"


def make_array_from_list(lst, ArrayWrapper):
    """
    Given a Python list and an element type (one of "string", "integer", "number", "boolean", "null"),
    return a Z3 array (of type Array(Int, T)) mapping indices 0..len(lst)-1 to the corresponding values.
    """
    if ArrayWrapper == ArrayWrapper_string:
        default_val = StringVal("")
        def convert(x): return StringVal(x)
    elif ArrayWrapper == ArrayWrapper_integer:
        default_val = IntVal(0)
        def convert(x): return IntVal(x)
    elif ArrayWrapper == ArrayWrapper_number:
        default_val = RealVal(0)
        def convert(x): return RealVal(x)
    elif ArrayWrapper == ArrayWrapper_boolean:
        default_val = BoolVal(False)
        def convert(x): return BoolVal(x)
    elif ArrayWrapper == ArrayWrapper_null:
        default_val = NullType.null
        def convert(x): return NullType.null
    else:
        raise NotImplementedError
    default_arr = K(IntSort(), default_val)  # default value
    arr_term = default_arr
    for i, elem in enumerate(lst):
        arr_term = Store(arr_term, i, convert(elem))
    return arr_term


def build_constraints(var, schema):
    """
    Recursively build Z3 constraints from a JSON Schema.
    Supported keywords include:
      - "enum", "const"
      - "anyOf", "allOf", "oneOf"
      - "not"
      - "if", "then", "else"
      - Type-specific keywords:
            * string: {"pattern", "minLength", "maxLength"}
            * number: {"multipleOf", "minimum", "exclusiveMinimum", "maximum", "exclusiveMaximum"}
            * integer: {"multipleOf", "minimum", "exclusiveMinimum", "maximum", "exclusiveMaximum"}
            * array: {"items", "minItems", "maxItems"}
            * boolean, null
    Raises NotImplementedError for any keyword outside SUPPORTED_KEYWORDS and
    ANNOTATION_KEYWORDS.
    """
    unsupported = set(schema) - SUPPORTED_KEYWORDS - ANNOTATION_KEYWORDS
    if unsupported:
        raise NotImplementedError(f"ERROR: schema keywords {sorted(unsupported)} not implemented")

    constraint = True

    # Global enum constraint: only the values of the variable's own type can match.
    if "enum" in schema:
        values = [value_to_z3(var.sort(), e) for e in schema["enum"]]
        constraint = And(constraint, Or([var == v for v in values if v is not None]))

    # const: a single allowed value.
    if "const" in schema:
        value = value_to_z3(var.sort(), schema["const"])
        constraint = And(constraint, var == value if value is not None else False)

    # anyOf: disjunction of subschemas.
    if "anyOf" in schema:
        branch_constraints = [build_constraints(var, subschema) for subschema in schema["anyOf"]]
        constraint = And(constraint, Or(branch_constraints))

    # allOf: all subschemas must hold.
    if "allOf" in schema:
        all_constraints = [build_constraints(var, subschema) for subschema in schema["allOf"]]
        constraint = And(constraint, And(all_constraints))

    # oneOf: exactly one subschema must hold.
    if "oneOf" in schema:
        oneof_constraints = [build_constraints(var, subschema) for subschema in schema["oneOf"]]
        constraint = And(constraint, Sum([If(c, 1, 0) for c in oneof_constraints]) == 1)

    # not: the subschema must not hold.
    if "not" in schema:
        constraint = And(constraint, Not(build_constraints(var, schema["not"])))

    # if/then/else: conditional constraints.
    if "if" in schema:
        if_constraint = build_constraints(var, schema["if"])
        if "then" in schema:
            then_constraint = build_constraints(var, schema["then"])
            constraint = And(constraint, Implies(if_constraint, then_constraint))
        if "else" in schema:
            else_constraint = build_constraints(var, schema["else"])
            constraint = And(constraint, Implies(Not(if_constraint), else_constraint))

    # Type check.
    if "type" in schema:
        t = schema["type"]
        t_list = []
        if isinstance(t, list):
            t_list = t
        else:
            t_list.append(t)
        type_constraint = []
        for t in t_list:
            if t == "string":
                type_constraint.append(var.sort() == StringSort())
            elif t == "array":
                type_constraint.append(Or([var.sort() == aw for aw in ARRAY_WRAPPERS]))
            elif t == "integer":
                if search_all_types() and var.sort() == RealSort():
                    # A number with an integral value is an integer too.
                    type_constraint.append(IsInt(var))
                else:
                    type_constraint.append(var.sort() == IntSort())
            elif t == "number":
                type_constraint.append(var.sort() == RealSort() or (search_all_types() and var.sort() == IntSort()))
            elif t == "boolean":
                type_constraint.append(var.sort() == BoolSort())
            elif t == "null":
                type_constraint.append(var.sort() == NullType)
            elif search_all_types():
                if t == "object":
                    type_constraint.append(var.sort() == JsonObject)
                else:
                    raise NotImplementedError(f"ERROR: type {t} not implemented")
        constraint = And(constraint, Or(type_constraint))

    # Type-specific constraints.
    if var.sort() == StringSort():
        if "pattern" in schema:
            pat = schema["pattern"]
            # jsonschema enforces "pattern" with re.search, so the language
            # modelled here is the searched one, not a whole-string match.
            regex = regex_to_z3_expr_search(pat)
            constraint = And(constraint, InRe(var, regex))
        if "minLength" in schema:
            constraint = And(constraint, Length(var) >= schema["minLength"])
        if "maxLength" in schema:
            constraint = And(constraint, Length(var) <= schema["maxLength"])
    elif var.sort() in ARRAY_WRAPPERS:
        a_accessor, len_accessor = ARRAY_WRAPPER_ACCESSORS[var.sort()]
        constraint = And(constraint, len_accessor(var) >= 0)
        if "minItems" in schema:
            constraint = And(constraint, len_accessor(var) >= schema["minItems"])
        if "maxItems" in schema:
            constraint = And(constraint, len_accessor(var) <= schema["maxItems"])
        if "items" in schema:
            items_schema = schema["items"]
            i = Int('i')
            constraint = And(constraint, ForAll(i, Implies(And(i >= 0, i < len_accessor(var)),
                                                           build_constraints(Select(a_accessor(var), i), items_schema))))
    elif var.sort() == IntSort():
        if "multipleOf" in schema:
            m = schema["multipleOf"]
            constraint = And(constraint, var % m == 0)
        if "exclusiveMinimum" in schema:
            constraint = And(constraint, var > schema["exclusiveMinimum"])
        if "minimum" in schema:
            constraint = And(constraint, var >= schema["minimum"])
        if "exclusiveMaximum" in schema:
            constraint = And(constraint, var < schema["exclusiveMaximum"])
        if "maximum" in schema:
            constraint = And(constraint, var <= schema["maximum"])
    elif var.sort() == RealSort():
        if "multipleOf" in schema:
            m = schema["multipleOf"]
            k = Int('k_mult')
            constraint = And(constraint, Exists(k, var == RealVal(m) * k))
        if "exclusiveMinimum" in schema:
            constraint = And(constraint, var > schema["exclusiveMinimum"])
        if "minimum" in schema:
            constraint = And(constraint, var >= schema["minimum"])
        if "exclusiveMaximum" in schema:
            constraint = And(constraint, var < schema["exclusiveMaximum"])
        if "maximum" in schema:
            constraint = And(constraint, var <= schema["maximum"])
    elif var.sort() == BoolSort():
        pass
    elif var.sort() == NullType:
        constraint = And(constraint, var == NullType.null)

    return constraint


SOLVER_SAT = "sat"
SOLVER_UNSAT = "unsat"
SOLVER_UNDECIDED = "undecided"


def solve_schema(schema):
    """
    Given a JSON Schema (as a dict), determine if there is a value that satisfies it.
    Chooses a top-level Z3 variable based on the schema's "type" or by inferring from an "enum".
    Returns (SOLVER_SAT, model, var) when a satisfying value was found,
    (SOLVER_UNSAT, None, var) when there is provably none, and
    (SOLVER_UNDECIDED, None, var) when no candidate type could be built, the
    solver timed out, or the schema used a construct that cannot be translated.
    """
    var_list = []
    # Determine the top-level type.
    if "type" in schema:
        t = schema["type"]
        t_list = []
        if isinstance(t, list):
            t_list = t
        else:
            t_list.append(t)
        for t in t_list:
            if t == "string":
                var_list.append(String('x'))
            elif t == "array":
                # Choose an array wrapper based on the "items" type if provided.
                if "items" in schema and "type" in schema["items"]:
                    item_type = schema["items"]["type"]
                    if item_type == "string":
                        var_list.append(Const('x', ArrayWrapper_string))
                    elif item_type == "integer":
                        var_list.append(Const('x', ArrayWrapper_integer))
                    elif item_type == "number":
                        var_list.append(Const('x', ArrayWrapper_number))
                    elif item_type == "boolean":
                        var_list.append(Const('x', ArrayWrapper_boolean))
                    elif item_type == "null":
                        var_list.append(Const('x', ArrayWrapper_null))
                    else:
                        for aw in ARRAY_WRAPPERS:
                            var_list.append(Const('x', aw))
                else:
                    for aw in ARRAY_WRAPPERS:
                        var_list.append(Const('x', aw))
            elif t == "integer":
                var_list.append(Int('x'))
            elif t == "number":
                var_list.append(Real('x'))
            elif t == "boolean":
                var_list.append(Bool('x'))
            elif t == "null":
                var_list.append(Const('x', NullType))
    else:
        # Infer type from enum if provided.
        if "enum" in schema and schema["enum"]:
            first = schema["enum"][0]
            if isinstance(first, list):
                # Infer element type.
                if len(first) > 0:
                    sample = first[0]
                    if isinstance(sample, str):
                        var_list.append(Const('x', ArrayWrapper_string))
                    elif isinstance(sample, int):
                        var_list.append(Const('x', ArrayWrapper_integer))
                    elif isinstance(sample, float):
                        var_list.append(Const('x', ArrayWrapper_number))
                    elif isinstance(sample, bool):
                        var_list.append(Const('x', ArrayWrapper_boolean))
                    elif sample is None:
                        var_list.append(Const('x', ArrayWrapper_null))
                    else:
                        for aw in ARRAY_WRAPPERS:
                            var_list.append(Const('x', aw))
                else:
                    for aw in ARRAY_WRAPPERS:
                        var_list.append(Const('x', aw))
            elif isinstance(first, str):
                var_list.append(String('x'))
            elif isinstance(first, int):
                var_list.append(Int('x'))
            elif isinstance(first, float):
                var_list.append(Real('x'))
            elif isinstance(first, bool):
                var_list.append(Bool('x'))
            elif first is None:
                var_list.append(Const('x', NullType))
        else:
            var_list = [String('x'), Int('x'), Real('x'), Bool('x'), Const('x', NullType)]
            for aw in ARRAY_WRAPPERS:
                var_list.append(Const('x', aw))
            if search_all_types():
                var_list.append(Const('x', JsonObject))

    undecided = False
    var = None
    for var in var_list:
        try:
            cons = build_constraints(var, schema)
            s = Solver()
            s.add(cons)
            s.set("timeout", 5000)
            result = s.check()
            if result == sat:
                model = s.model()
                return SOLVER_SAT, model, var
            if result == unknown:
                undecided = True
                print(f"solve_schema: solver gave up on {var.sort()}: {s.reason_unknown()}", file=sys.stderr)
        except Exception as e:
            # An untranslatable regex or an unsupported keyword leaves this
            # branch unproved; it does not make the branch unsatisfiable.
            undecided = True
            print(f"solve_schema: cannot decide {var.sort()}: {e}", file=sys.stderr)
    if var is None:
        # No candidate type matched the schema, so nothing was ever checked.
        undecided = True
    return (SOLVER_UNDECIDED if undecided else SOLVER_UNSAT), None, var


def security_policy_analysis(security_policy):
    warnings = []
    if security_policy is None:
        return warnings
    for tool_name, policies in security_policy.items():
        n = len(policies)
        for i in range(n):
            for j in range(i+1, n):
                for arg_name, restriction_1 in policies[i][2].items():
                    if arg_name in policies[j][2]:
                        restriction_2 = policies[j][2][arg_name]
                        # print(restriction_1, restriction_2)
                        if isinstance(restriction_1, dict) and isinstance(restriction_2, dict):  # json schema
                            schema = {
                                "allOf": [
                                    restriction_1,
                                    restriction_2
                                ]
                            }
                            status, model, var = solve_schema(schema)
                            if status == SOLVER_SAT:
                                warnings.append(f"Policy Warning: {restriction_1} and {restriction_2} overlap. Possible value: {model[var]}.")
                            elif status == SOLVER_UNDECIDED:
                                warnings.append(f"Policy Warning: cannot determine whether {restriction_1} and {restriction_2} overlap.")
    return warnings


def security_policy_subset_check(ori_policy, new_policy):
    """
    Check that every generated (priority 100) restriction in new_policy only
    admits values the matching restriction in ori_policy admits. Returns True
    only when that is proved; anything that cannot be decided returns False.

    Limitations:
      - Type changes are not detected by default. The counter example search
        is limited to the type of the original restriction (its "type", or the
        types of the enum and const values), so a new restriction that also admits
        values of another type, e.g. {"type": "string", "enum": ["a"]} ->
        {"type": "integer"}, passes. Set SECAGENT_SUBSET_CHECK_ALL_TYPES=true
        to search values of every type instead. That mode is stricter: a
        restriction without "type" admits values of every type, so replacing
        {"type": "string", "pattern": "^a"} by {"pattern": "^a"} is rejected.
      - Arrays are modelled as one-dimensional arrays whose elements share one
        scalar type. Nested arrays and arrays of mixed types are never
        searched, in either mode, so a widening that only shows on such values
        passes.
      - Objects are not modelled. Object keywords ("properties", "required",
        ...) make the check undecided, and with SECAGENT_SUBSET_CHECK_ALL_TYPES
        an object is only distinguished from the other types.
      - Regexes are translated over ASCII only, while Python matches str
        patterns over Unicode, so a widening that only shows on non-ASCII
        characters, e.g. "^[0-9]+$" -> "^\\d+$" (which also admits other
        decimal digits), passes.
      - A regex with a construct that cannot be translated (an interior ^ or $,
        \\b, lookarounds, backreferences, inline flags) makes the check undecided.
    """
    ori_policy_filtered = {tool: [p for p in policies if p[0] == 100] for tool, policies in ori_policy.items()}
    new_policy_filtered = {tool: [p for p in policies if p[0] == 100] for tool, policies in new_policy.items()}
    # if tool: [], [] is empty list, delete it.
    ori_policy_filtered = {tool: policies for tool, policies in ori_policy_filtered.items() if len(policies) > 0}
    new_policy_filtered = {tool: policies for tool, policies in new_policy_filtered.items() if len(policies) > 0}
    print(ori_policy_filtered, new_policy_filtered, file=sys.stderr)
    for tool, policies in list(ori_policy_filtered.items()) + list(new_policy_filtered.items()):
        if len(policies) > 1:
            print(f"Tool '{tool}' has {len(policies)} generated policy entries, expected one.", file=sys.stderr)
            return False
    for tool, new_policies in new_policy_filtered.items():
        if tool not in ori_policy_filtered:
            return False
    for tool, new_policies in new_policy_filtered.items():
        ori_policies = ori_policy_filtered[tool]
        print(ori_policies, new_policies, file=sys.stderr)
        for arg_name, restriction_1 in ori_policies[0][2].items():
            if arg_name not in new_policies[0][2]:
                return False
            restriction_2 = new_policies[0][2][arg_name]
            print(restriction_1, restriction_2, file=sys.stderr)
            if isinstance(restriction_1, dict) and isinstance(restriction_2, dict):  # json schema
                schema = {
                    "allOf": [
                        {"not": restriction_1},
                        restriction_2
                    ]
                }
                if not search_all_types():
                    var_type = None
                    if "type" in restriction_1:
                        var_type = restriction_1["type"]
                    elif "type" in restriction_2:
                        var_type = restriction_2["type"]
                    else:
                        # Without a "type", search the types of all enum and const
                        # values on both sides. {"enum": [None, "a"]} ->
                        # {"enum": [None, "b"]} must be rejected, which requires
                        # searching strings as well as null.
                        values = []
                        for restriction in (restriction_1, restriction_2):
                            values.extend(restriction.get("enum", []))
                            if "const" in restriction:
                                values.append(restriction["const"])
                        value_types = sorted({json_type_name(v) for v in values})
                        if value_types:
                            var_type = value_types
                    if var_type is not None:
                        schema["type"] = var_type
                        print("Found type:", var_type, file=sys.stderr)
                status, model, var = solve_schema(schema)
                if status == SOLVER_SAT:
                    print(f"Found counter example: {model[var]}", file=sys.stderr)
                    return False
                if status != SOLVER_UNSAT:
                    # Containment was not proved, so it cannot be assumed.
                    print(f"Cannot prove {restriction_2} is a subset of {restriction_1}.", file=sys.stderr)
                    return False
            else:
                if restriction_1 != restriction_2:
                    return False
    return True


if __name__ == "__main__":
    warnings = security_policy_analysis(
        security_policy={
            "send_money": [
                (1, 0, {"recipient": {"type": "string", "pattern": "UK12345678901234567890"}}, 0),
                (2, 1, {"recipient": {"type": "string", "pattern": "SE3550000000054910000003"}}, 0),
            ],
            "send_email": [
                (1, 0, {"recipient": {"type": "string", "pattern": "[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}"}}, 0),
                (2, 1, {"recipient": {"type": "string", "pattern": "agent@example.com"}}, 0),
            ]
        }
    )
    print(warnings)
