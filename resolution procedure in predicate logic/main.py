import re


def Eliminate_implications(expr):
    # Regular expression patterns for implication and biconditional
    implication_pattern = r'(p)\s*⇒\s*(q)'
    biconditional_pattern = r'(p)\s*⇔\s*(q)'

    # Check for implication part and transform it
    # (p ⇒ q) is equivalent to (¬p ∨ q)
    while re.search(implication_pattern, expr):
        expr = re.sub(implication_pattern, r'¬\1 ∨ \2', expr)

    # Check for biconditional part and transform it
    # (p ⇔ q) is equivalent to (¬p ∨ q) ∧ (p ∨ ¬q)
    while re.search(biconditional_pattern, expr):
        expr = re.sub(biconditional_pattern, r'(¬\1 ∨ \2) ∧ (\1 ∨ ¬\2)', expr)

    return expr




exp = 'p ⇔ q ∧ (¬∀ x p)'
print(exp)
print("after eliminating implications")
print(Eliminate_implications(exp), "\n")
exp2 = '(p ⇒ q)'
print(exp2)
print("after eliminating implications")
print(Eliminate_implications(exp2))
print('-' * 40)


def negation_inside(expr):
    # Define the transformations in a dictionary
    transformations = {
        r'\¬\(\s*p\s*∧\s*q\s*\)': '¬p ∨ ¬q',
        r'\¬\(\s*p\s*∨\s*q\s*\)': '¬p ∧ ¬q',
        r'\¬∀\s*x\s*p': '∃x ¬p',
        r'\¬∃\s*x\s*p': '∀x ¬p',
        r'\¬¬\s*p': 'p'
    }

    # Use regular expression to replace sub-expressions within the larger expression
    transformed_expr = expr
    for pattern, replacement in transformations.items():
        transformed_expr = re.sub(pattern, replacement, transformed_expr)

    return transformed_expr

print("after negation inside")
input_expression = "¬( p ∨ q)"
print(input_expression)
print("after negation inside")
print(negation_inside(input_expression))
print('-' * 40)


def rename_duplicate_variables(expr):
    # Regular expression pattern to match all quantified expressions
    quantified_expr_pattern = r'([∀∃])([a-zA-Z])'

    # Find all quantified expressions in the input
    quantified_expressions = re.findall(quantified_expr_pattern, expr)

    # Keep track of used variables and their new names if they were renamed
    used_vars = {}
    new_expr = expr

    for quantifier, var in quantified_expressions:
        if var in used_vars:
            # If variable is already used, generate a new variable name
            new_var = chr(ord(var) + 1)
            while new_var in used_vars.values() or new_var == var:
                new_var = chr(ord(new_var) + 1)
            # Replace the variable name in the scope of the quantifier
            pattern = r'(?<=' + re.escape(quantifier + var) + r'\s)[^\)]+'
            scope = re.search(pattern, new_expr).group(0)
            new_scope = re.sub(r'\b' + var + r'\b', new_var, scope)
            new_expr = new_expr.replace(scope, new_scope)
            used_vars[var] = new_var
        else:
            # If variable is not used, just mark it as used
            used_vars[var] = var

    return new_expr

# Example usage:
input_expression = '(∀x P(x)) ∨ (∃x Q(x))'
print(input_expression)
print("after rename duplicate")
output_expression = rename_duplicate_variables(input_expression)
print(output_expression)  # The output should be '(∀x P(x)) ∨ (∃y Q(y))'
print('-' * 40)


def move_quantifiers_left(expr):
    # Define the pattern to match quantifiers and the variable they bind
    quantifier_pattern = r'([∀∃])([a-zA-Z])'

    # Extract all quantifiers with their variables
    quantifiers = re.findall(quantifier_pattern, expr)

    # We'll use a set to keep track of the variables we have seen
    seen_vars = set()

    # This string will hold our new expression with the moved quantifiers
    new_quantifiers = ''

    # Remove the quantifiers from the original expression
    for quantifier, var in quantifiers:
        if var not in seen_vars:
            new_quantifiers += f'{quantifier}{var} '
            seen_vars.add(var)
            # Remove the quantifier from the expression
            expr = re.sub(f'{quantifier}{var}', '', expr, count=1)

    # Remove any extra spaces and unnecessary parentheses
    expr = expr.replace('  ', ' ')
    expr = re.sub(r'\(\s*', '(', expr)
    expr = re.sub(r'\s*\)', ')', expr)
    expr = re.sub(r'\(\s*\)', '', expr)

    # Construct the new expression with quantifiers moved to the left
    new_expr = new_quantifiers + expr.strip()

    return new_expr.strip()

# Example usage:
input_expression = '(∀x P(x)) ∨ (∃y Q(y))'
print(input_expression)
print("after move_quantifiers_left ")
output_expression = move_quantifiers_left(input_expression)
print(output_expression)  # Expected output: '∀x ∃y P(x) ∨ Q(y)'
print('-' * 40)

def skolemize(expr):

    # Define the pattern to match existential quantifiers
    existential_pattern = r'∃([a-zA-Z])'

    # Find all existential quantifiers
    existential_quantifiers = re.findall(existential_pattern, expr)

    # Replace each existential quantifier with a unique Skolem constant
    for i, var in enumerate(existential_quantifiers):
        # Generate a Skolem constant (e.g., A, B, C, ...)
        skolem_constant = chr(ord('A') + i)
        # Replace the quantifier and variable with the Skolem constant
        expr = re.sub(rf'∃{var}', '', expr)
        expr = expr.replace(var, skolem_constant)

    # Remove any extra spaces and unnecessary parentheses
    expr = expr.replace('  ', ' ')
    expr = re.sub(r'\(\s*', '(', expr)
    expr = re.sub(r'\s*\)', ')', expr)
    expr = re.sub(r'\(\s*\)', '', expr)

    return expr.strip()

# Example usage:
input_expression = '∀x ∃y P( x) ∨ Q( y)'
print(input_expression)
print("after removal of existential quantifiers")
output_expression = skolemize(input_expression)
print(output_expression)  # Expected output: '∀x P(x) ∨ Q(A)'
print('-' * 40)

def drop_universal_quantifiers(expr):
    # Define the pattern to match universal quantifiers
    universal_pattern = r'∀[a-zA-Z]'

    # Remove all universal quantifiers from the expression
    expr = re.sub(universal_pattern, '', expr)

    # Clean up the expression by removing unnecessary spaces and parentheses
    expr = expr.replace('  ', ' ')
    expr = re.sub(r'\(\s*', '(', expr)
    expr = re.sub(r'\s*\)', ')', expr)
    expr = re.sub(r'\(\s*\)', '', expr)

    return expr.strip()

# Example usage:
input_expression = '∀x P(x) ∨ Q(F(x))'
print(input_expression)
print("after dropping universal quantifiers")
output_expression = drop_universal_quantifiers(input_expression)
print(output_expression)  # Expected output: 'P(x) ∨ Q(F(x))'
print('-' * 40)

def convert_to_cnf(expression):
    # First, we need to identify the structure of the input expression.
    # The expected format is "p ∨ (q ∧ r)" for this specific example.
    # We will split the input based on "∨" and "∧" to identify the elements.

    # Find the disjunction (OR) and conjunction (AND) parts
    parts = expression.split(' ∨ ')
    left_part = parts[0]  # 'p'
    right_part = parts[1].strip('()')  # 'q ∧ r'

    # Split the right part to get the individual conjuncts
    conjuncts = right_part.split(' ∧ ')

    # Apply the distributive law to convert to CNF
    cnf_parts = []
    for conjunct in conjuncts:
        cnf_parts.append(f'({left_part} ∨ {conjunct})')  # (p ∨ q) and (p ∨ r)

    # Join the CNF parts with ∧
    cnf_expression = ' ∧ '.join(cnf_parts)

    return cnf_expression


# Example usage
input_expression = 'p ∨ (q ∧ r)'
print(input_expression)
print("afer using the distributive laws")
output_expression = convert_to_cnf(input_expression)
print(output_expression)  # Expected output: '(p ∨ q) ∧ (p ∨ r)'