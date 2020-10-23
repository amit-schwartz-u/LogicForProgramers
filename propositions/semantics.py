# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""
import itertools
from typing import AbstractSet, Iterable, Iterator, Mapping, Sequence, Tuple

from tabulate import tabulate
from propositions.syntax import *
from propositions.proofs import *

#: A model for propositional-logic formulas, a mapping from variable names to
#: truth values.
Model = Mapping[str, bool]


def is_model(model: Model) -> bool:
	"""Checks if the given dictionary is a model over some set of variables.

	Parameters:
		model: dictionary to check.

	Returns:
		``True`` if the given dictionary is a model over some set of
		variables,
		``False`` otherwise.
	"""
	for key in model:
		if not is_variable(key):
			return False
	return True


def variables(model: Model) -> AbstractSet[str]:
	"""Finds all variables over which the given model is defined.

	Parameters:
		model: model to check.

	Returns:
		A set of all variables over which the given model is defined.
	"""
	assert is_model(model)
	return model.keys()


def evaluate(formula: Formula, model: Model) -> bool:
	"""Calculates the truth value of the given formula in the given model.

	Parameters:
		formula: formula to calculate the truth value of.
		model: model over (possibly a superset of) the variables of the
		formula,
			to calculate the truth value in.

	Returns:
		The truth value of the given formula in the given model.

	Examples:
		>>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': False})
		True

		>>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': True})
		False
	"""
	assert is_model(model)
	assert formula.variables().issubset(variables(model))
	# Task 2.1
	if is_variable(formula.root):
		return model.get(formula.root)
	elif formula.root == "F":
		return False
	elif formula.root == "T":
		return True
	elif is_unary(formula.root):
		return not evaluate(formula.first, model)
	elif formula.root == "&":
		return evaluate(formula.first, model) and evaluate(formula.second,
														   model)
	elif formula.root == "|":
		return evaluate(formula.first, model) or evaluate(formula.second,
														  model)
	elif formula.root == "->":
		left_res = evaluate(formula.first, model)
		right_res = evaluate(formula.second, model)
		if left_res is False or (left_res and right_res):
			return True
		return False


def all_models(variables: Sequence[str]) -> Iterable[Model]:
	"""Calculates all possible models over the given variables.

	Parameters:
		variables: variables over which to calculate the models.

	Returns:
		An iterable over all possible models over the given variables.
		The
		order
		of the models is lexicographic according to the order of the given
		variables, where False precedes True.

	Examples:
		>>> list(all_models(['p', 'q']))
		[{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True,
		'q': False}, {'p': True, 'q': True}]

		>>> list(all_models(['q', 'p']))
		[{'q': False, 'p': False}, {'q': False, 'p': True}, {'q': True,
		'p': False}, {'q': True, 'p': True}]
	"""
	for v in variables:
		assert is_variable(v)  # Task 2.2
	res = []
	for assignment in itertools.product([False, True], repeat=len(variables)):
		cur_dict = {}
		for i, v in enumerate(variables):
			cur_dict[v] = assignment[i]
		res.append(cur_dict)
	return res


def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
	"""Calculates the truth value of the given formula in each of the 
	given
	model.

	Parameters:
		formula: formula to calculate the truth value of.
		models: iterable over models to calculate the truth value in.

	Returns:
		An iterable over the respective truth values of the given 
		formula in
		each of the given models, in the order of the given models.

	Examples:
		>>> list(truth_values(Formula.parse('~(p&q76)'), all_models(['p', 
		'q76'])))
		[True, True, True, False]
	"""  # Task 2.3
	res = []
	for model in models:
		res.append(evaluate(formula, model))
	return res


def print_truth_table(formula: Formula) -> None:
	"""Prints the truth table of the given formula, with variable-name 
	columns
	sorted alphabetically.

	Parameters:
		formula: formula to print the truth table of.

	Examples:
		>>> print_truth_table(Formula.parse('~(p&q76)'))
		| p | q76 | ~(p&q76) |
		|---|-----|----------|
		| F | F   | T        |
		| F | T   | T        |
		| T | F   | T        |
		| T | T   | F        |
	"""  # Task 2.4
	vars = formula.variables()
	headers = [var for var in vars]
	headers.append(str(formula))
	models = all_models(vars)
	rows = []
	for model in models:
		cur_row = []
		for v in model.values():
			if v:
				cur_row.append("T")
			else:
				cur_row.append("F")
		if evaluate(formula, model):
			cur_row.append("T")
		else:
			cur_row.append("F")
		rows.append(cur_row)
	print(tabulate(rows, headers=headers, tablefmt='github'))


def is_tautology(formula: Formula) -> bool:
	"""Checks if the given formula is a tautology.

	Parameters:
		formula: formula to check.

	Returns:
		``True`` if the given formula is a tautology, ``False`` otherwise.
	"""  # Task 2.5a
	for model in all_models(formula.variables()):
		if not evaluate(formula, model):
			return False
	return True


def is_contradiction(formula: Formula) -> bool:
	"""Checks if the given formula is a contradiction.

	Parameters:
		formula: formula to check.

	Returns:
		``True`` if the given formula is a contradiction, ``False`` 
		otherwise.
	"""  # Task 2.5b
	return is_tautology(Formula('~', formula))


def is_satisfiable(formula: Formula) -> bool:
	"""Checks if the given formula is satisfiable.

	Parameters:
		formula: formula to check.

	Returns:
		``True`` if the given formula is satisfiable, ``False`` otherwise.
	"""  # Task 2.5c
	return not is_contradiction(formula)


def _synthesize_for_model(model: Model) -> Formula:
	"""Synthesizes a propositional formula in the form of a single
	conjunctive
	clause that evaluates to ``True`` in the given model, and to
	``False`` in
	any other model over the same variables.

	Parameters:
		model: model over a nonempty set of variables, in which the
		synthesized
			formula is to hold.

	Returns:
		The synthesized formula.
	"""
	assert is_model(model)
	assert len(model.keys()) > 0  # Task 2.6
	return _synthesize_for_model_helper(list(model.keys()), model)


def _synthesize_for_model_helper(vars, model):
	cur_formula = Formula(vars[0])
	if not model.get(vars[0]):
		cur_formula = Formula('~', cur_formula)
	if len(vars) == 1:
		return cur_formula
	else:
		return Formula('&', cur_formula,
					   _synthesize_for_model_helper(vars[1:], model))


def synthesize(variables: Sequence[str], values: Iterable[bool]) -> Formula:
	"""Synthesizes a propositional formula in DNF over the given
	variables,
	that has the specified truth table.

	Parameters:
		variables: nonempty set of variables for the synthesized formula.
		values: iterable over truth values for the synthesized formula in
		every
			possible model over the given variables, in the order
			returned by
			`all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

	Returns:
		The synthesized formula.

	Examples:
		>>> formula = synthesize(['p', 'q'], [True, True, True, False])
		>>> for model in all_models(['p', 'q']):
		...     evaluate(formula, model)
		True
		True
		True
		False
	"""
	assert len(variables) > 0  # Task 2.7
	is_first = True
	cur_formula = None
	for i, model in enumerate(all_models(variables)):
		if values[i]:
			if is_first:
				cur_formula = _synthesize_for_model(model)
				is_first = False
			else:
				cur_formula = Formula('|', cur_formula,
									  _synthesize_for_model(model))
	if cur_formula is None:
		return Formula("&", Formula(variables[0]),
					   Formula("~", Formula(variables[0])))
	return cur_formula


def _synthesize_for_all_except_model(model: Model) -> Formula:
	"""Synthesizes a propositional formula in the form of a single
	disjunctive
	clause that evaluates to ``False`` in the given model, and to
	``True`` in
	any other model over the same variables.

	Parameters:
		model: model over a nonempty set of variables, in which the
		synthesized
			formula is to hold.

	Returns:
		The synthesized formula.
	"""
	assert is_model(model)
	assert len(model.keys()) > 0  # Optional Task 2.8


def synthesize_cnf(variables: Sequence[str],
				   values: Iterable[bool]) -> Formula:
	"""Synthesizes a propositional formula in CNF over the given
	variables,
	that has the specified truth table.

	Parameters:
		variables: nonempty set of variables for the synthesized formula.
		values: iterable over truth values for the synthesized formula in
		every
			possible model over the given variables, in the order
			returned by
			`all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

	Returns:
		The synthesized formula.

	Examples:
		>>> formula = synthesize_cnf(['p', 'q'], [True, True, True,
		False])
		>>> for model in all_models(['p', 'q']):
		...     evaluate(formula, model)
		True
		True
		True
		False
	"""
	assert len(variables) > 0  # Optional Task 2.9


# Tasks for Chapter 4

def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
	"""Checks if the given inference rule holds in the given model.

	Parameters:
		rule: inference rule to check.
		model: model to check in.

	Returns:
		``True`` if the given inference rule holds in the given model,
		``False``
		otherwise.

	Examples:
		>>> evaluate_inference(InferenceRule([Formula('p')], Formula(
		'q')),
		...                    {'p': True, 'q': False})
		False

		>>> evaluate_inference(InferenceRule([Formula('p')], Formula(
		'q')),
		...                    {'p': False, 'q': False})
		True
	"""
	assert is_model(model)  # Task 4.2


def is_sound_inference(rule: InferenceRule) -> bool:
	"""Checks if the given inference rule is sound, i.e., whether its
	conclusion is a semantically correct implication of its assumptions.

	Parameters:
		rule: inference rule to check.

	Returns:
		``True`` if the given inference rule is sound, ``False`` 
		otherwise.
	"""  # Task 4.3
