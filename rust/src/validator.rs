// Library for validating rules.

use std::result::Result;

use crate::base::CountType;
use crate::config::Config;
use crate::count_expr::{CountExpr, Function, VarSubst, VarSubstError, Variable, VAR_N};
use crate::tm::TM;

use thiserror::Error;

type RuleIdType = usize;
const INDUCTION_VAR: Variable = VAR_N;

#[derive(Debug, Clone)]
pub enum ProofStep {
    // Apply an integer count of base TM steps.
    TMSteps(CountType),
    // Apply a rule with the given ID and variable assignments.
    RuleStep {
        rule_id: RuleIdType,
        var_assignment: VarSubst,
    },
    // Apply this rule via induction.
    InductiveStep(VarSubst),
    // End proof early and treat it like a success. (For debugging.)
    Admit,
}

#[derive(Debug)]
pub enum Proof {
    // A simple non-inductive proof.
    Simple(Vec<ProofStep>),
    // An inductive proof (where we prove a base case, and then an induction step).
    Inductive {
        // TODO: Induction variable.
        // var: Variable,
        proof_base: Vec<ProofStep>,
        proof_inductive: Vec<ProofStep>,
    },
    // A proof splitting a variable into different cases modulo `proof_cases.len()`.
    ModularCases {
        var: Variable,
        proof_cases: Vec<Vec<ProofStep>>,
    },
}

#[derive(Debug)]
pub struct Rule {
    init_config: Config,
    final_config: Config,
    proof: Proof,
}

#[derive(Debug)]
pub struct RuleSet {
    tm: TM,
    // Mapping from rule ID to Rule.
    // Rule n may only use rules with id < n (or induction).
    rules: Vec<Rule>,
}

// Errors while validating one step in a rule.
#[derive(Error, Debug)]
enum StepValidationError {
    #[error("Error applying {1} TM steps to config {0}: {2}")]
    TMStepError(Config, CountType, String),
    #[error("Rule {0} is not yet defined")]
    RuleNotYetDefined(RuleIdType),
    #[error("Induction variable must decrease correctly")]
    InductionVarNotDecreasing,
    #[error("Configuration does not match rule initial config {0} vs. {1}: {2}")]
    RuleConfigMismatch(Config, Config, String),
    #[error("Variable substitution error: {0}")]
    VarSubstError(#[from] VarSubstError),
    #[error("Inductive step in non-inductive proof")]
    InductiveStepInNonInductiveProof,
}

// Errors while evaluating a rule part (base or inductive).
#[derive(Error, Debug)]
enum ProofValidationError {
    #[error("Step {step_num}: {error}")]
    StepError {
        step_num: usize,
        error: StepValidationError,
    },
    #[error("Final configuration mismatch: {actual_config} != {expected_config}")]
    FinalConfigMismatch {
        actual_config: Config,
        expected_config: Config,
    },
}

// Errors while evaluating a rule.
#[derive(Error, Debug)]
enum RuleValidationError {
    // Failure in a Proof::Simple proof.
    #[error("{0}")]
    Simple(ProofValidationError),
    // Failure in a Proof::Inductive proof_base.
    #[error("Base: {0}")]
    Base(ProofValidationError),
    // Failure in a Proof::Inductive proof_inductive.
    #[error("Induction: {0}")]
    Induction(ProofValidationError),
    #[error("No modular cases are defined")]
    NoModularCases,
    // Failure in a Proof::ModularCases proof_case.
    #[error("Case {0}: {1}")]
    ModularCase(usize, ProofValidationError),
}

#[allow(dead_code)]
#[derive(Error, Debug)]
#[error("Validation error: Rule {rule_id}: {error}")]
struct ValidationError {
    rule_id: RuleIdType,
    error: RuleValidationError,
}

fn try_apply_rule(
    config: &Config,
    rule: &Rule,
    var_subst: &VarSubst,
) -> Result<Config, StepValidationError> {
    let init_config = rule
        .init_config
        .subst(var_subst)
        .map_err(StepValidationError::VarSubstError)?;
    let final_config = rule
        .final_config
        .subst(var_subst)
        .map_err(StepValidationError::VarSubstError)?;
    config
        .replace(&init_config, &final_config)
        .map_err(|err| StepValidationError::RuleConfigMismatch(config.clone(), init_config, err))
}

fn apply_proof_step(
    tm: &TM,
    mut config: Config,
    proof_step: &ProofStep,
    prev_rules: &[Rule],
    // Only used in inductive proofs.
    // Should be set to None for non-inductive proofs (including induction base cases).
    induction_rule: Option<&Rule>,
) -> Result<Config, StepValidationError> {
    match proof_step {
        ProofStep::TMSteps(n) => {
            // Apply n base TM steps.
            config
                .step_n(tm, *n)
                .map_err(|err| StepValidationError::TMStepError(config.clone(), *n, err))?;
            Ok(config)
        }
        ProofStep::RuleStep {
            rule_id,
            var_assignment,
        } => {
            if *rule_id >= prev_rules.len() {
                return Err(StepValidationError::RuleNotYetDefined(*rule_id));
            }
            try_apply_rule(&config, &prev_rules[*rule_id], var_assignment)
        }
        ProofStep::InductiveStep(var_assignment) => {
            // Only allow induction rules in inductive proofs.
            let Some(this_rule) = induction_rule else {
                return Err(StepValidationError::InductiveStepInNonInductiveProof);
            };

            // Ensure that the induction variable is decreasing.
            // Note: When doing an inductive proof, we start by replacing n <- n+1 and
            // then only allow any uses of the rule itself with n <- n.
            if var_assignment.get(&INDUCTION_VAR) != Some(&CountExpr::var_plus(INDUCTION_VAR, 0)) {
                return Err(StepValidationError::InductionVarNotDecreasing);
            }
            try_apply_rule(&config, this_rule, var_assignment)
        }
        ProofStep::Admit => Ok(config),
    }
}

// Apply all steps in a proof and validate that the final config is correct.
fn validate_proof(
    tm: &TM,
    init_config: Config,
    proof_steps: &Vec<ProofStep>,
    final_config: Config,
    prev_rules: &[Rule],
    // Only used in inductive proofs.
    // Should be set to None for non-inductive proofs (including induction base cases).
    induction_rule: Option<&Rule>,
) -> Result<(), ProofValidationError> {
    let mut config = init_config;
    for (step_num, step) in proof_steps.iter().enumerate() {
        if matches!(step, ProofStep::Admit) {
            return Ok(());
        }
        config = apply_proof_step(tm, config, step, prev_rules, induction_rule)
            .map_err(|error| ProofValidationError::StepError { step_num, error })?;
    }
    if config.equivalent_to(&final_config) {
        Ok(())
    } else {
        Err(ProofValidationError::FinalConfigMismatch {
            actual_config: config,
            expected_config: final_config,
        })
    }
}

fn validate_rule(tm: &TM, rule: &Rule, prev_rules: &[Rule]) -> Result<(), RuleValidationError> {
    match &rule.proof {
        Proof::Simple(proof) => validate_proof(
            tm,
            rule.init_config.clone(),
            &proof,
            rule.final_config.clone(),
            prev_rules,
            None,
        )
        .map_err(RuleValidationError::Simple),
        Proof::Inductive {
            proof_base,
            proof_inductive,
        } => {
            // Validate the base case (n <- 0).
            let base_subst = VarSubst::single(INDUCTION_VAR, 0.into());
            validate_proof(
                tm,
                rule.init_config.subst(&base_subst).unwrap(),
                &proof_base,
                rule.final_config.subst(&base_subst).unwrap(),
                prev_rules,
                None,
            )
            .map_err(RuleValidationError::Base)?;

            // Validate the inductive case (n <- m+1).
            let induct_subst =
                VarSubst::single(INDUCTION_VAR, CountExpr::var_plus(INDUCTION_VAR, 1));
            validate_proof(
                tm,
                rule.init_config.subst(&induct_subst).unwrap(),
                &proof_inductive,
                rule.final_config.subst(&induct_subst).unwrap(),
                prev_rules,
                Some(rule),
            )
            .map_err(RuleValidationError::Induction)
        }
        Proof::ModularCases { var, proof_cases } => {
            if proof_cases.is_empty() {
                return Err(RuleValidationError::NoModularCases);
            }
            let var_expr = CountExpr::var_plus(*var, 0);
            let modulus = proof_cases.len().try_into().unwrap();

            for (i, proof) in proof_cases.iter().enumerate() {
                // Validate the i'th modular case (var <- modulus*var+i).
                let f = Function::affine(modulus, i.try_into().unwrap());
                let case_subst = VarSubst::single(*var, f.apply(var_expr.clone()));
                validate_proof(
                    tm,
                    rule.init_config.subst(&case_subst).unwrap(),
                    proof,
                    rule.final_config.subst(&case_subst).unwrap(),
                    prev_rules,
                    None,
                )
                .map_err(|err| RuleValidationError::ModularCase(i, err))?;
            }

            Ok(())
        }
    }
}

// Validate a rule set.
#[allow(dead_code)]
fn validate_rule_set(rule_set: &RuleSet) -> Result<(), ValidationError> {
    for (rule_id, rule) in rule_set.rules.iter().enumerate() {
        validate_rule(&rule_set.tm, rule, &rule_set.rules[..rule_id])
            .map_err(|error| ValidationError { rule_id, error })?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::{str::FromStr, vec};

    use crate::count_expr::{Function, RecursiveExpr};

    use super::*;

    // Helper functions to create proof steps of various kinds.
    fn base_step(num_steps: CountType) -> ProofStep {
        ProofStep::TMSteps(num_steps)
    }

    fn load_vars(var_assign: &[(&str, &str)]) -> VarSubst {
        let mut var_subst = VarSubst::default();
        for (var, count) in var_assign {
            var_subst.insert(
                Variable::from_str(var).unwrap(),
                CountExpr::from_str(count).unwrap(),
            );
        }
        var_subst
    }

    fn rule_step(rule_num: RuleIdType, var_assign: &[(&str, &str)]) -> ProofStep {
        ProofStep::RuleStep {
            rule_id: rule_num,
            var_assignment: load_vars(var_assign),
        }
    }

    fn chain_step(rule_num: RuleIdType, num_reps: &str) -> ProofStep {
        rule_step(rule_num, &[("n", num_reps)])
    }

    fn induction_step(var_assign: &[(&str, &str)]) -> ProofStep {
        let mut var_subst = load_vars(var_assign);
        // Add default n->n inductive bit.
        var_subst.insert(INDUCTION_VAR, INDUCTION_VAR.into());
        ProofStep::InductiveStep(var_subst)
    }

    fn induction_step_expr(var_assign: &[(Variable, CountExpr)]) -> ProofStep {
        let mut var_subst = VarSubst::default();
        for (var, expr) in var_assign {
            var_subst.insert(var.clone(), expr.clone());
        }
        // Add default n->n inductive bit.
        var_subst.insert(INDUCTION_VAR, INDUCTION_VAR.into());
        ProofStep::InductiveStep(var_subst)
    }

    fn simple_rule(start: &str, end: &str, steps: CountType) -> Rule {
        Rule {
            init_config: Config::from_str(start).unwrap(),
            final_config: Config::from_str(end).unwrap(),
            proof: Proof::Simple(vec![base_step(steps)]),
        }
    }

    // Helper function to create a simple chain rule for which:
    //    A) The base case is trivial.
    //    B) The inductive case is simple inductive step + `steps` TM steps.
    // Note: We currently need to do induction step first in order to work
    // around fragile tape comparison issues for blocks. Specifically, the fact that
    //      0^1 1^1 01^n  ==  01^n+1
    // which our current tape comparison cannot equate.
    fn chain_rule(start: &str, end: &str, steps: CountType) -> Rule {
        Rule {
            init_config: Config::from_str(start).unwrap(),
            final_config: Config::from_str(end).unwrap(),
            proof: Proof::Inductive {
                proof_base: vec![],
                proof_inductive: vec![induction_step(&[]), base_step(steps)],
            },
        }
    }

    #[test]
    fn test_validate_rule_trivial() {
        // Validate a very trivial rule which does nothing.
        let tm = TM::from_str("1RB1LB_1LA1RZ").unwrap();
        let rule = Rule {
            init_config: Config::from_str("0^inf 1^138 B> 0 1^2 0^inf").unwrap(),
            final_config: Config::from_str("0^inf 1^138 B> 0 1^2 0^inf").unwrap(),
            proof: Proof::Simple(vec![]),
        };
        let prev_rules = vec![];
        validate_rule(&tm, &rule, &prev_rules).unwrap();
    }

    #[test]
    fn test_validate_rule_simple() {
        // Validate a very simple rule that just performs a few steps on a tape with no variables.
        // BB(2) champion
        let tm = TM::from_str("1RB1LB_1LA1RZ").unwrap();
        // BB2 runs for 6 steps.
        let rule = Rule {
            init_config: Config::new(),
            final_config: Config::from_str("0^inf 1^2 Z> 1^2 0^inf").unwrap(),
            proof: Proof::Simple(vec![base_step(6)]),
        };
        let prev_rules = vec![];
        validate_rule(&tm, &rule, &prev_rules).unwrap();
    }

    #[test]
    fn test_validate_rule_chain() {
        // Validate a chain rule.
        //      https://www.sligocki.com/2021/07/17/bb-collatz.html#chain-step
        let tm = TM::from_str("1RB1LD_1RC1RB_1LC1LA_0RC0RD").unwrap();
        // 0^n <C  ->  <C 1^n
        let rule = Rule {
            init_config: Config::from_str("0^n <C").unwrap(),
            final_config: Config::from_str("<C 1^n").unwrap(),
            proof: Proof::Inductive {
                // Base case is trivial:  0^0 <C  ==  <C 1^0
                proof_base: vec![],
                proof_inductive: vec![
                    // 0^n+1 <C  ->  0^n <C 1
                    base_step(1),
                    // 0^n <C 1  ->  <C 1^n 1  ==  <C 1^n+1
                    induction_step(&[]),
                ],
            },
        };
        let prev_rules = vec![];
        validate_rule(&tm, &rule, &prev_rules).unwrap();
    }

    #[test]
    fn test_validate_rule_level1() {
        // Validate a "level 1" rule (rule built only on chain rules). This is Rule 1x from:
        //      https://www.sligocki.com/2022/02/27/bb-recurrence-relations.html
        let rule_set = RuleSet {
            tm: TM::from_str("1RB0LB1LA_2LC2LB2LB_2RC2RA0LC").unwrap(),
            rules: vec![
                chain_rule("C> 0^n", "2^n C>", 1),
                chain_rule("2^n <C", "<C 0^n", 1),
                // Rule 1x: 0^inf <C 0^a 2^n  ->  0^inf <C 0^a+2n
                Rule {
                    init_config: Config::from_str("0^inf <C 0^a 2^n").unwrap(),
                    final_config: Config::from_str("0^inf <C 0^a+2n").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 0^inf <C 0^a 2^n+1  ->  0^inf 2 C> 0^a 2^n+1
                            base_step(1),
                            // 0^inf 2 C> 0^a 2^n+1  ->  0^inf 2^a+1 C> 2^n+1
                            chain_step(0, "a"),
                            // 0^inf 2^a+1 C> 2^n+1  ->  0^inf 2^a+1 <C 0 2^n
                            base_step(1),
                            // 0^inf 2^a+1 <C 0 2^n  ->  0^inf <C 0^a+2 2^n
                            chain_step(1, "a+1"),
                            // Induction: 0^inf <C 0^a+2 2^n  ->  0^inf <C 0^a+2n+2
                            induction_step(&[("a", "a+2")]),
                        ],
                    },
                },
            ],
        };
        validate_rule_set(&rule_set).unwrap();
    }

    #[test]
    fn test_validate_rule_counter() {
        // Validate a binary counter rule which uses the inductive hypothesis twice!
        //      See: https://www.sligocki.com/2022/06/14/counter-induction.html
        let rule_set = RuleSet {
            tm: TM::from_str("1RB1LA_0LC0RB_0LD0LB_1RE---_1LE1LA").unwrap(),
            rules: vec![
                chain_rule("1^n <A", "<A 1^n", 1),
                chain_rule("B> 1^n", "0^n B>", 1),
                // Rule P(n): 0^n 1 00 B> 0  ->  1^n+1 00 B> 0
                Rule {
                    init_config: Config::from_str("0^n 1 0 0 B> 0").unwrap(),
                    final_config: Config::from_str("1^n+1 0 0 B> 0").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 0^n+1 1 00 B> 0  ->  0 1^n+1 00 B> 0
                            induction_step(&[]),
                            // 0 1^n+1 00 B> 0  --(5)-->  0 1^n+1 <A 110
                            base_step(5),
                            // 0 1^n+1 <A 110  -->  0 <A 1^n+3 0
                            chain_step(0, "n+1"),
                            // 0 <A 1^n+3 0  --(1)-->  1 B> 1^n+3 0
                            base_step(1),
                            // 1 B> 1^n+3 0  --(5)-->  0^n+3 B> 0
                            chain_step(1, "n+3"),
                            // 0^n+3 B> 0  --(8)-->  1 0^n 1 00 B> 0
                            base_step(8),
                            // 1 0^n 1 00 B> 0  -->  1^n+2 00 B> 0
                            induction_step(&[]),
                        ],
                    },
                },
                // Infinite Rule: 0^inf 1 00 B> 0  ->  0^inf 1^n+1 00 B> 0
                Rule {
                    init_config: Config::from_str("0^inf 1 0 0 B> 0").unwrap(),
                    final_config: Config::from_str("0^inf 1^n+1 0 0 B> 0").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1 00 B> 0  ->  0^inf 1^n+2 00 B> 0
                        rule_step(2, &[("n", "n")]),
                    ]),
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[test]
    fn test_bouncer() {
        // Simple Bouncer
        // 1RB0RC_0LC---_1RD1RC_0LE1RA_1RD1LE

        fn f(n: CountExpr) -> CountExpr {
            CountExpr::RecursiveExpr(RecursiveExpr {
                func: Box::new(Function {
                    bound_var: "z".parse().unwrap(),
                    expr: "2z+4".parse().unwrap(),
                }),
                num_repeats: Box::new(n),
                base: Box::new(0.into()),
            })
        }

        let rule_set = RuleSet {
            tm: TM::from_str("1RB0RC_0LC---_1RD1RC_0LE1RA_1RD1LE").unwrap(),
            rules: vec![
                chain_rule("C> 1^n", "1^n C>", 1), // 0
                chain_rule("1^n <E", "<E 1^n", 1), // 1
                // 2: 0^inf 1^a A> 1^b 0^inf  -->  0^inf 1^{a+2} A> 1^{b-1} 0^inf  in 2b+4 steps
                Rule {
                    init_config: Config::from_str("0^inf 1^a A> 1^n 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1^a+2n A> 0^inf").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 0^inf 1^a A> 1^n+1 0^inf
                            base_step(1),
                            // 0^inf 1^a 0 C> 1^n 0^inf
                            chain_step(0, "n"),
                            // 0^inf 1^a 0 1^n C> 0^inf
                            base_step(2),
                            // 0^inf 1^a 0 1^n+1 <E 0^inf
                            chain_step(1, "n+1"),
                            // 0^inf 1^a 0 <E 1^n+1 0^inf
                            base_step(2),
                            // 0^inf 1^a+2 A> 1^n 0^inf
                            induction_step(&[("a", "a+2")]),
                        ],
                    },
                },
                // 3: 0^inf 1^a A> 0^inf  -->  0^inf 1^{2a + 6} A> 0^inf    in a^2 + 12a + 35 steps
                Rule {
                    init_config: Config::from_str("0^inf 1^a A> 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1^2a+4 A> 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1^a A> 0^inf
                        base_step(5),
                        // 0^inf 1^a+2 <E 0^inf
                        chain_step(1, "a+2"),
                        // 0^inf <E 1^a+2 0^inf
                        base_step(2),
                        // 0^inf 1^2 A> 1^a+1 0^inf
                        rule_step(2, &[("a", "2"), ("n", "a+1")]),
                        // 0^inf 1^2f+4 A> 0^inf
                    ]),
                },
                // Infinite Rule
                Rule {
                    init_config: Config::new(),
                    final_config: Config::from_str("0^inf 1^x A> 0^inf")
                        .unwrap()
                        .subst(&VarSubst::single(
                            Variable::from_str("x").unwrap(),
                            f("n".parse().unwrap()),
                        ))
                        .unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![
                            // TODO: Need 0^inf 1^{(λz.2z+4)^0 0} A> == 0^inf 1^0 A> == 0^inf A>
                            ProofStep::Admit,
                        ],
                        proof_inductive: vec![
                            induction_step_expr(&[]),
                            // 0^inf 1^{f^n(0)} A> 0^inf
                            ProofStep::RuleStep {
                                rule_id: 3,
                                var_assignment: VarSubst::single(
                                    Variable::from_str("a").unwrap(),
                                    f("n".parse().unwrap()),
                                ),
                            },
                            // 0^inf 1^{f^n+1(0)} A> 0^inf
                        ],
                    },
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[test]
    fn test_bb5() {
        // Marxen's BB(5) Champion
        //      1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA
        // A(n) = 0^inf <A 1^n 0^inf

        let rule_set = RuleSet {
            tm: TM::from_str("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA").unwrap(),
            rules: vec![
                chain_rule("B> 1^n", "1^n B>", 1),    // 0
                chain_rule("1^n <D", "<D 1^n", 1),    // 1
                chain_rule("1^3n <A", "<A 001^n", 3), // 2
                // 3: 0^inf <A 1^a 001^n  ->  0^inf <A 1^5n+a
                //      R3(a, n) = (A0 B1^a+k B0 C0 D1^a+k+4 D0)^{k: 0 -> n-1}
                Rule {
                    init_config: Config::from_str("0^inf <A 1^a 001^n").unwrap(),
                    final_config: Config::from_str("0^inf <A 1^5n+a").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // <A 1^a 001^n+1
                            base_step(1),
                            // 1 B> 1^a 001^n+1
                            chain_step(0, "a"),
                            base_step(3),
                            // 1^a+3 <D 1 001^n
                            chain_step(1, "a+3"),
                            base_step(1),
                            // <A 1^a+5 001^n
                            induction_step(&[("n", "n"), ("a", "a+5")]),
                        ],
                    },
                },
                // 4: A(3k) -> A(5k+6)
                //      A0 B1^3k B0 C0 D0 (A1 C1 E1)^k+1 R3(0, k+1)
                Rule {
                    init_config: Config::from_str("0^inf <A 1^3k 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf <A 1^5k+6 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // <A 1^3k
                        base_step(1),
                        // 1 B> 1^3k
                        chain_step(0, "3k"),
                        base_step(3),
                        // 1^3k+3 <A 1
                        chain_step(2, "k+1"),
                        // <A 001^k+1 1
                        rule_step(3, &[("a", "0"), ("n", "k+1")]),
                        // <A 1^5k+5 1
                    ]),
                },
                // 5: A(3k+1) -> A(5k+9)
                //      A0 B1^3k B0 C0 D0 (A1 C1 E1)^k+1 A1 C0 D1 D1 D0 R3(3, k+1)
                Rule {
                    init_config: Config::from_str("0^inf <A 1^3k+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf <A 1^5k+9 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // <A 1^3k+1
                        base_step(1),
                        // 1 B> 1^3k+1
                        chain_step(0, "3k+1"),
                        base_step(3),
                        // 1^3k+4 <A 1
                        chain_step(2, "k+1"),
                        // 1 <A 001^k+1 1
                        base_step(5),
                        // <A 1^3 001^k+1 1
                        rule_step(3, &[("a", "3"), ("n", "k+1")]),
                        // <A 1^5k+8 1
                    ]),
                },
                // 6: A(3k+2) -> Halt
                //      A0 B1^3k B0 C0 D0 (A1 C1 E1)^k+1 A1 C1 E0
                Rule {
                    init_config: Config::from_str("0^inf <A 1^3k+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1 Z> 01 001^k+1 1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // <A 1^3k+2
                        base_step(1),
                        // 1 B> 1^3k+2
                        chain_step(0, "3k+2"),
                        base_step(3),
                        // 1^3k+5 <A 1
                        chain_step(2, "k+1"),
                        // 11 <A 001^k+1 1
                        base_step(3),
                    ]),
                },
                // Halting trajectory
                Rule {
                    init_config: Config::from_str("0^inf <A 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1 Z> 01 001^4095 1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(4, &[("k", "0")]), // A(0)
                        rule_step(4, &[("k", "2")]), // A(6)
                        rule_step(5, &[("k", "5")]), // A(16)
                        rule_step(5, &[("k", "11")]),
                        rule_step(5, &[("k", "21")]),
                        rule_step(4, &[("k", "38")]),
                        rule_step(5, &[("k", "65")]),
                        rule_step(5, &[("k", "111")]),
                        rule_step(4, &[("k", "188")]),
                        rule_step(5, &[("k", "315")]),
                        rule_step(4, &[("k", "528")]),
                        rule_step(4, &[("k", "882")]),
                        rule_step(4, &[("k", "1472")]), // A(4416)
                        rule_step(5, &[("k", "2455")]), // A(7366)
                        rule_step(6, &[("k", "4094")]), // A(12284)
                    ]),
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[test]
    fn test_62_uni_t15() {
        // Pavel's BB(6) > 10^^15 Champion
        //      https://www.sligocki.com/2022/06/21/bb-6-2-t15.html
        //      1RB0LD_1RC0RF_1LC1LA_0LE1RZ_1LF0RB_0RC0RE
        // D(n, m) = 0^inf 1 0^n <D 0 1^3m+4 0^inf

        // f1(x) = 3x+7
        // f2(x, y) = f1^x(y)  = ((2y+7) 3^x - 7)/2
        fn f2(x: CountExpr, y: CountExpr) -> CountExpr {
            CountExpr::RecursiveExpr(RecursiveExpr {
                func: Box::new(Function {
                    bound_var: "x".parse().unwrap(),
                    expr: "3x+7".parse().unwrap(),
                }),
                num_repeats: Box::new(x),
                base: Box::new(y),
            })
        }

        let rule_set = RuleSet {
            tm: TM::from_str("1RB0LD_1RC0RF_1LC1LA_0LE1RZ_1LF0RB_0RC0RE").unwrap(),
            rules: vec![
                chain_rule("B> 1^3n", "0^3n B>", 3), // 0
                chain_rule("0^n <C", "<C 1^n", 1),   // 1
                // 2: 0^n <A 1^3k+1 0^inf  ->  <A 1^3n+3k+1 0^inf
                Rule {
                    init_config: Config::from_str("0^n <A 1^3k+1 0^inf").unwrap(),
                    final_config: Config::from_str("<A 1^3n+3k+1 0^inf").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 0^n+1 <A 1^3k+1
                            base_step(1),
                            // 0^n 1 B> 1^3k+1
                            chain_step(0, "k"),
                            // 0^n 1 0^3k B> 1
                            base_step(3),
                            // 0^n 1 0^3k+2 <C 1
                            chain_step(1, "3k+2"),
                            base_step(1),
                            // 0^n <A 1^3k+4
                            induction_step(&[("n", "n"), ("k", "k+1")]),
                        ],
                    },
                },
                // 3: D(a+4, b) -> D(a, 3b+7)
                Rule {
                    init_config: Config::from_str("0^4 <D 0 1^3b+4 0^inf").unwrap(),
                    final_config: Config::from_str("<D 0 1^9b+25 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        base_step(12),
                        // 1 B> 1^3b+8
                        chain_step(0, "b+2"),
                        // 1 0^3b+6 B> 1^2
                        base_step(5),
                        // 1 0^3b+8 <A 1
                        rule_step(2, &[("n", "3b+8"), ("k", "0")]),
                        // 1 <A 1^3b+25 0^inf
                        base_step(1),
                    ]),
                },
                // 4: D(4k+r, b) -> D(r, f^k(b))
                //      for f(b) = 3b+7
                //          f^k(b) = ((2b+7) 3^k - 7)/2
                Rule {
                    init_config: Config::from_str("0^4n <D 0 1^3b+4 0^inf").unwrap(),
                    final_config: Config::from_str("<D 0 1^3x+4 0^inf")
                        .unwrap()
                        .subst(&VarSubst::single(
                            Variable::from_str("x").unwrap(),
                            f2("n".parse().unwrap(), "b".parse().unwrap()),
                        ))
                        .unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            rule_step(3, &[("b", "b")]),
                            induction_step(&[("n", "n"), ("b", "3b+7")]),
                        ],
                    },
                },
                // 5: D(4k, 1) -> Halt( 3/2 (9 3^k - 7) + 5 )
                Rule {
                    init_config: Config::from_str("1 0^4k <D 0 1^7 0^inf").unwrap(),
                    final_config: Config::from_str("1 Z> 0 1^3x+4 0^inf")
                        .unwrap()
                        .subst(&VarSubst::single(
                            Variable::from_str("x").unwrap(),
                            f2("k".parse().unwrap(), 1.into()),
                        ))
                        .unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(4, &[("n", "k"), ("b", "1")]),
                        // 1 <D 0 1^3x+4   for x = f^k(1)
                        base_step(1),
                    ]),
                },
                // 6: TODO: D(4k+1, 1) -> D( ? )
                // Rule {
                //     init_config: Config::from_str("1 0^4k+1 <D 0 1^7 0^inf").unwrap(),
                //     final_config: Config::from_str("?")
                //         .unwrap()
                //         .subst(&VarSubst::single(
                //             Variable::from_str("x").unwrap(),
                //             f2("k".parse().unwrap(), 1.into()),
                //         ))
                //         .unwrap(),
                //     proof: Proof::Simple(vec![
                //         rule_step(4, &[("n", "k"), ("b", "1")]),
                //         // 10 <D 0 1^3x+4   for x = f^k(1)
                //         base_step(6),
                //         // 1 B> 1^3x+6
                //         ProofStep::RuleStep {
                //             rule_id: 0,
                //             var_assignment: VarSubst::from(&[(
                //                 "n".parse().unwrap(),
                //                 VarSum::from_str("x+2").unwrap().subst(&VarSubst::single(
                //                     Variable::from_str("x").unwrap(),
                //                     f2("k".parse().unwrap(), 1.into()),
                //                 )),
                //             )]),
                //         },
                //     ]),
                // },
                // TODO: Halting trajectory
                // Rule {
                //     init_config: Config::new(),
                //     // TODO: Eval x
                //     final_config: Config::from_str("0^inf 1 Z> 1^x 0^inf").unwrap(),
                //     proof: Proof::Simple(vec![
                //         base_step(53),
                //         // D(5, 1)
                //         rule_step(6, &[("k", "1")]),
                //         // D(35, 1)
                //     ]),
                // },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[test]
    fn test_hydra() {
        // https://www.sligocki.com/2024/05/10/bb-2-5-is-hard.html
        // 1RB3RB---3LA1RA_2LA3RA4LB0LB0LA
        // Let A(a, b) = 0^inf <B 0^a 3^b 2 0^inf

        let rule_set = RuleSet {
            tm: TM::from_str("1RB3RB1RZ3LA1RA_2LA3RA4LB0LB0LA").unwrap(),
            rules: vec![
                chain_rule("3^n <A", "<A 3^n", 1),     // 0
                chain_rule("3^n <B", "<B 0^n", 1),     // 1
                chain_rule("1 B> 3^n", "3^n 1 B>", 3), // 2
                // 3:  0^inf 3^a 1 A> 00  -->  0^inf 3^a+3 1 A>
                Rule {
                    init_config: Config::from_str("0^inf 3^a 1 A> 0^2n").unwrap(),
                    final_config: Config::from_str("0^inf 3^3n+a 1 A>").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 0^inf 3^a 1 A> 00
                            base_step(12),
                            // 0^inf 3^a <A 332
                            chain_step(0, "a"),
                            // 0^inf <A 3^a+2 2
                            base_step(1),
                            // 0^inf 1 B> 3^a+2 2
                            chain_step(2, "a+2"),
                            // 0^inf 3^a+2 1 B> 2
                            base_step(3),
                            // 0^inf 3^a+3 1 A>
                            induction_step(&[("a", "a+3")]),
                        ],
                    },
                },
                // Collatz rules
                // A(2n, 0)  -->  Halt(3n+3)
                Rule {
                    init_config: Config::from_str("0^inf <B 0^2n 3^0 2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 3^3n+1 11 Z> 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf <B 0^2n 2 0^inf
                        base_step(5),
                        // 0^inf 3 1 A> 0^2n 2 0^inf
                        rule_step(3, &[("a", "1"), ("n", "n")]),
                        // 0^inf 3^3n+1 1 A> 2 0^inf
                        base_step(1),
                        // 0^inf 3^3n+1 11 Z> 0^inf
                    ]),
                },
                // A(2n, b+1)  -->  A(3n+3, b)
                Rule {
                    init_config: Config::from_str("0^inf <B 0^2n 3^b+1 2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf <B 0^3n+3 3^b 2 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf <B 0^2n 3^b+1 2 0^inf
                        base_step(5),
                        // 0^inf 3 1 A> 0^2n 3^b+1 2 0^inf
                        rule_step(3, &[("a", "1"), ("n", "n")]),
                        // 0^inf 3^3n+1 1 A> 3^b+1 2 0^inf
                        base_step(3),
                        // 0^inf 3^3n+2 <B 0 3^b 2 0^inf
                        chain_step(1, "3n+2"),
                        // 0^inf <B 0^3n+3 3^b 2 0^inf
                    ]),
                },
                // A(2n+1, b)  -->  A(3n+3, b+2)
                Rule {
                    init_config: Config::from_str("0^inf <B 0^2n+1 3^b 2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf <B 0^3n+3 3^b+2 2 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf <B 0^2n+1 3^b 2 0^inf
                        base_step(5),
                        // 0^inf 3 1 A> 0^2n+1 3^b 2 0^inf
                        rule_step(3, &[("a", "1"), ("n", "n")]),
                        // 0^inf 3^3n+1 1 A> 0 3^b 2 0^inf
                        base_step(1),
                        // 0^inf 3^3n+1 1 1 B> 3^b 2 0^inf
                        chain_step(2, "b"),
                        // 0^inf 3^3n+1 1 3^b 1 B> 2 0^inf
                        base_step(13),
                        // 0^inf 3^3n+1 1 3^b+3 <A 2 0^inf
                        chain_step(0, "b+3"),
                        // 0^inf 3^3n+1 1 <A 3^b+3 2 0^inf
                        base_step(2),
                        // 0^inf 3^3n+2 <B 0 3^b+3 2 0^inf
                        chain_step(1, "3n+2"),
                        // 0^inf <B 0^3n+3 3^b+2 2 0^inf
                    ]),
                },
                // 0^inf A> 0^inf  --(19)-->  A(3, 0)
                Rule {
                    init_config: Config::new(),
                    final_config: Config::from_str("0^inf <B 0^3 3^0 2 0^inf").unwrap(),
                    proof: Proof::Simple(vec![base_step(19)]),
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[test]
    fn test_hydra2() {
        // Hydra compiled into 2 states by @dyuan01
        // https://discord.com/channels/960643023006490684/1084047886494470185/1247560072427474955
        //      0RE1RG_1RH0LD_0LA0LF_0LB1LJ_1RB1RA_1RE1LC_0LF---_1LF0LI_0LD0LC_1RE0RH
        //
        // Left:
        //   0: 00
        //   1: 01
        //   3: 11
        // Right:
        //   0: 00
        //   2: 11
        //   3: 10
        //   4: 01
        // States:
        //   A>: A>
        //   B>: B>
        //   <A: <C
        //   <B: <D

        let rule_set = RuleSet {
            tm: TM::from_str(
                "0RE1RG_1RH0LD_0LA0LF_0LB1LJ_1RB1RA_1RE1LC_0LF1RZ_1LF0LI_0LD0LC_1RE0RH",
            )
            .unwrap(),
            rules: vec![
                chain_rule("11^n <C", "<C 10^n", 2),       // 0
                chain_rule("11^n <D", "<D 00^n", 4),       // 1
                chain_rule("01 B> 10^n", "11^n 01 B>", 6), // 2
                // 3:  0^inf 3^a 1 A> 00  -->  0^inf 3^a+3 1 A>
                Rule {
                    init_config: Config::from_str("0^inf 11^a 01 A> 00^2n").unwrap(),
                    final_config: Config::from_str("0^inf 11^3n+a 01 A>").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 0^inf 3^a 1 A> 00
                            base_step(31),
                            // 0^inf 3^a <A 332
                            chain_step(0, "a"),
                            // 0^inf <A 3^a+2 2
                            base_step(3),
                            // 0^inf 1 B> 3^a+2 2
                            chain_step(2, "a"),
                            chain_step(2, "2"),
                            // 0^inf 3^a+2 1 B> 2
                            base_step(6),
                            // 0^inf 3^a+3 1 A>
                            induction_step(&[("a", "a+3")]),
                        ],
                    },
                },
                // Collatz rules
                // 4: A(2n, 0)  -->  Halt(3n+3)
                Rule {
                    init_config: Config::from_str("0^inf <D 00^2n 10^0 11 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 11^3n+1 01 11 Z> 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf <B 0^2n 2 0^inf
                        base_step(13),
                        // 0^inf 3 1 A> 0^2n 2 0^inf
                        rule_step(3, &[("a", "1"), ("n", "n")]),
                        // 0^inf 3^3n+1 1 A> 2 0^inf
                        base_step(2),
                        // 0^inf 3^3n+1 11 Z> 0^inf
                    ]),
                },
                simple_rule("<D 00", "<D 00", 0), // 5
                // 6: A(2n, b+1)  -->  A(3n+3, b)
                Rule {
                    init_config: Config::from_str("0^inf <D 00^2n 10^b+1 11 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf <D 00^3n+3 10^b 11 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf <B 0^2n 3^b+1 2 0^inf
                        base_step(13),
                        // 0^inf 3 1 A> 0^2n 3^b+1 2 0^inf
                        rule_step(3, &[("a", "1"), ("n", "n")]),
                        // 0^inf 3^3n+1 1 A> 3^b+1 2 0^inf
                        base_step(7),
                        rule_step(5, &[]),
                        // 0^inf 3^3n+2 <B 0 3^b 2 0^inf
                        chain_step(1, "3n+2"),
                        // 0^inf <B 0^3n+3 3^b 2 0^inf
                    ]),
                },
                // 7: A(2n+1, b)  -->  A(3n+3, b+2)
                Rule {
                    init_config: Config::from_str("0^inf <D 00^2n+1 10^b 11 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf <D 00^3n+3 10^b+2 11 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf <B 0^2n+1 3^b 2 0^inf
                        base_step(13),
                        // 0^inf 3 1 A> 0^2n+1 3^b 2 0^inf
                        rule_step(3, &[("a", "1"), ("n", "n")]),
                        // 0^inf 3^3n+1 1 A> 0 3^b 2 0^inf
                        base_step(2),
                        // 0^inf 3^3n+1 1 1 B> 3^b 2 0^inf
                        chain_step(2, "b"),
                        // 0^inf 3^3n+1 1 3^b 1 B> 2 0^inf
                        base_step(33),
                        // 0^inf 3^3n+1 1 3^b+3 <A 2 0^inf
                        chain_step(0, "b+3"),
                        // 0^inf 3^3n+1 1 <A 3^b+3 2 0^inf
                        base_step(4),
                        rule_step(5, &[]),
                        // 0^inf 3^3n+2 <B 0 3^b+3 2 0^inf
                        chain_step(1, "3n+2"),
                        // 0^inf <B 0^3n+3 3^b+2 2 0^inf
                    ]),
                },
                // 0^inf A> 0^inf  -->  A(3, 0)
                Rule {
                    init_config: Config::new(),
                    final_config: Config::from_str("0^inf <D 00^3 10^0 11 0^inf").unwrap(),
                    proof: Proof::Simple(vec![base_step(51)]),
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[test]
    fn test_antihydra() {
        // https://wiki.bbchallenge.org/wiki/Antihydra
        // 1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA
        // Let A(a+4, b) = 0^inf 1^b 0 1^a E> 0^inf

        let rule_set = RuleSet {
            tm: TM::from_str("1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_1RZ0RA").unwrap(),
            rules: vec![
                chain_rule("A> 1^n", "1^n A>", 1), // 0
                chain_rule("1^n <C", "<C 1^n", 1), // 1
                chain_rule("E> 1^n", "1^n E>", 1), // 2
                // 3: 11 <B 0 1^c 0^inf -> <B 0 1^c+3 0^inf
                Rule {
                    init_config: Config::from_str("1^2n <B 0 1^c 0^inf").unwrap(),
                    final_config: Config::from_str("<B 0 1^c+3n 0^inf").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 11 <B 0 1^c $
                            base_step(6),
                            // 101 A> 1^c $
                            chain_step(0, "c"),
                            base_step(2),
                            // 1 0 1^c+2 <C $
                            chain_step(1, "c+2"),
                            base_step(2),
                            // <B 0 1^c+3
                            induction_step(&[("c", "c+3")]),
                        ],
                    },
                },
                // 4: A(2a, b) -> A(3a, b+2)
                Rule {
                    init_config: Config::from_str("0^inf 1^b 0 1^2a+2 E> 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1^b+2 0 1^3a+5 E> 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        base_step(9),
                        // $ 1^b 0 1^2a <B 0 111 $
                        rule_step(3, &[("n", "a"), ("c", "3")]),
                        // $ 1^b 0 <B 0 1^3a+3 $
                        base_step(1),
                        chain_step(1, "b"),
                        base_step(5),
                        // $ 1 E> 1^b+2 00 1^3a+3 $
                        chain_step(2, "b+2"),
                        base_step(6),
                        chain_step(2, "3a+3"),
                    ]),
                },
                // 5: A(2a+1, 0) -> Halt
                Rule {
                    init_config: Config::from_str("0^inf 1^0 0 1^2a+3 E> 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1 Z> 110 1^3a+3 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        base_step(9),
                        // $ 1^2a+1 <B 0 111 $
                        rule_step(3, &[("n", "a"), ("c", "3")]),
                        // $ 1 <B 0 1^3a+3 $
                        base_step(3),
                    ]),
                },
                // 6: A(2a+1, b+1) -> A(3a+1, b)
                Rule {
                    init_config: Config::from_str("10 1^2a+3 E> 0^inf").unwrap(),
                    final_config: Config::from_str("0 1^3a+6 E> 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        base_step(9),
                        // 10 1^2a+1 <B 0 111 $
                        rule_step(3, &[("n", "a"), ("c", "3")]),
                        // 101 <B 0 1^3a+3 $
                        base_step(8),
                        // 0 111 E> 1^3a+3 $
                        chain_step(2, "3a+3"),
                    ]),
                },
                // 0^inf A> 0^inf  -->  A(8, 0)  --->  A(202, 10)
                Rule {
                    init_config: Config::new(),
                    final_config: Config::from_str("0^inf 1^10 0 1^198 E> 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        base_step(11),
                        // A(8, 0)
                        rule_step(4, &[("a", "1"), ("b", "0")]),
                        // A(12, 2)
                        rule_step(4, &[("a", "3"), ("b", "2")]),
                        // A(18, 4)
                        rule_step(4, &[("a", "6"), ("b", "4")]),
                        // A(27, 6)
                        rule_step(6, &[("a", "10"), ("b", "6")]),
                        // A(40, 5)
                        rule_step(4, &[("a", "17"), ("b", "5")]),
                        // A(60, 7)
                        rule_step(4, &[("a", "27"), ("b", "7")]),
                        // A(90, 9)
                        rule_step(4, &[("a", "42"), ("b", "9")]),
                        // A(135, 11)
                        rule_step(6, &[("a", "64"), ("b", "11")]),
                        // A(202, 10)
                    ]),
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[test]
    fn test_bigfoot() {
        // https://www.sligocki.com/2023/10/16/bb-3-3-is-hard.html
        // 1RB2RA1LC_2LC1RB2RB_---2LA1LA
        // Let A(a, b, c) = 0^inf 12^a 11^b <A 11^c 0^inf

        let rule_set = RuleSet {
            tm: TM::from_str("1RB2RA1LC_2LC1RB2RB_1RZ2LA1LA").unwrap(),
            rules: vec![
                chain_rule("A> 1^n", "2^n A>", 1),   // 0
                chain_rule("2^2n <A", "<A 1^2n", 2), // 1
                // 2: 1^n <A 1^2c 2^n  -->  <A 1^2c+2n
                Rule {
                    init_config: Config::from_str("1^n <A 1^2c 2^n").unwrap(),
                    final_config: Config::from_str("<A 1^2c+2n").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 1 <A 1^2c 2
                            base_step(1),
                            // 2 A> 1^2c 2
                            chain_step(0, "2c"),
                            // 2^2c+1 A> 2
                            base_step(2),
                            chain_step(1, "c"),
                            // <A 1^2c+2
                            induction_step(&[("c", "c+1")]),
                        ],
                    },
                },
                // 3: 1^3n <A 1^2c+1 2^n  -->  <A 1^2c+1+4n
                Rule {
                    init_config: Config::from_str("1^3n <A 1^2c+1 2^n").unwrap(),
                    final_config: Config::from_str("<A 1^2c+1+4n").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 111 <A 1^2c+1 2
                            base_step(1),
                            // 11 2 A> 1^2c+1 2
                            chain_step(0, "2c+1"),
                            // 11 2^2c+2 A> 2
                            base_step(2),
                            chain_step(1, "c"),
                            // 11 2 <A 1^2c+2
                            base_step(5),
                            // <A 1^2c+5
                            induction_step(&[("c", "c+2")]),
                        ],
                    },
                },
                // 4:  1^12 <A 1^2c 0^inf  -->  <A 1^2c+16 0^inf
                Rule {
                    init_config: Config::from_str("1^12n <A 1^2c 0^inf").unwrap(),
                    final_config: Config::from_str("<A 1^2c+16n 0^inf").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 1^12 <A 1^2c 0^inf
                            base_step(1),
                            chain_step(0, "2c"),
                            // 1^11 2^2c+1 A> 0^inf
                            base_step(3),
                            // 1^11 2^2c+1 <A 22 0^inf
                            chain_step(1, "c"),
                            // 1^11 2 <A 1^2c 22 0^inf
                            base_step(5),
                            // 1^9 <A 1^2c+3 22 0^inf
                            rule_step(3, &[("n", "2"), ("c", "c+1")]),
                            // 1^3 <A 1^2c+11 0^inf
                            base_step(1),
                            chain_step(0, "2c+11"),
                            // 1^2 2^2c+12 A> 0^inf
                            base_step(3),
                            // 1^2 2^2c+12 <A 22 0^inf
                            chain_step(1, "c+6"),
                            // 1^2 <A 1^2c+12 22 0^inf
                            rule_step(2, &[("n", "2"), ("c", "c+6")]),
                            // <A 1^2c+16 0^inf
                            induction_step(&[("c", "c+8")]),
                        ],
                    },
                },
                // 5:  0^inf 12^n <A  -->  0^inf 12^n 1 B>
                Rule {
                    init_config: Config::from_str("0^inf 12^n <A").unwrap(),
                    final_config: Config::from_str("0^inf 12^n 1 B>").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![base_step(1)],
                        proof_inductive: vec![
                            // 0^inf 12^n+1 <A
                            base_step(2),
                            // 0^inf 12^n <A 21
                            induction_step(&[]),
                            // 0^inf 12^n 1 B> 21
                            base_step(2),
                        ],
                    },
                },
                chain_rule("B> 1^n", "1^n B>", 1), // 6
                // Collatz rules
                // A(a, 6k, c+1)  -->  A(a, 8k+c, 2)
                Rule {
                    init_config: Config::from_str("0^inf 12^a 1^12k <A 1^2c+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 12^a 1^16k+2c <A 1^4 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 12^a 1^12k <A 1^2c+2 0^inf
                        rule_step(4, &[("n", "k"), ("c", "c+1")]),
                        // 0^inf 12^a <A 1^2c+2+16k 0^inf
                        rule_step(5, &[("n", "a")]),
                        // 0^inf 12^a 1 B> 1^2c+2+16k 0^inf
                        chain_step(6, "2c+2+16k"),
                        // 0^inf 12^a 1^16k+2c+3 B> 0^inf
                        base_step(12),
                        // 0^inf 12^a 1^16k+2c <A 1^4 0^inf
                    ]),
                },
                // A(a, 6k+1, c+1)  -->  A(a, 8k+c, 2)
                Rule {
                    init_config: Config::from_str("0^inf 12^a 1^12k+2 <A 1^2c+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 12^a+1 1^16k+2c <A 1^6 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 12^a 1^12k+2 <A 1^2c+2 0^inf
                        rule_step(4, &[("n", "k"), ("c", "c+1")]),
                        // 0^inf 12^a 11 <A 1^2c+2+16k 0^inf
                        ProofStep::Admit, // TODO
                    ]),
                },
                // TODO: Rest of rules:
                // ...
                // 0^inf A> 0^inf  --(69)-->  A(2, 1, 2)
                Rule {
                    init_config: Config::new(),
                    final_config: Config::from_str("0^inf 12^2 1^2 <A 1^4 0^inf").unwrap(),
                    proof: Proof::Simple(vec![base_step(69)]),
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[test]
    fn test_finned3() {
        // "Irregular" TM "Finned #3"
        // https://discuss.bbchallenge.org/t/10756090-finned-3-is-irregular/137
        // 1RB1RE_1LC1RB_0RA0LD_1LB1LD_---0RA
        // C(n, m) = 0^inf 10^n A> 0 1^m 0^inf

        let rule_set = RuleSet {
            tm: TM::from_str("1RB1RE_1LC1RB_0RA0LD_1LB1LD_1RZ0RA").unwrap(),
            rules: vec![
                chain_rule("B> 1^n", "1^n B>", 1),   // 0
                chain_rule("1^n <D", "<D 1^n", 1),   // 1
                chain_rule("A> 1^2n", "10^n A>", 2), // 2
                // 3: 10^n <D 1^a 0 -> <D 1^a+n 0 1^n
                //      R3(n, a) = (D0 B1^a+k+1 B0 C1 D1^a+k+1)^{k:0 -> n-1}
                Rule {
                    init_config: Config::from_str("10^n <D 1^a 0").unwrap(),
                    final_config: Config::from_str("<D 1^a+n 0 1^n").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 10^n+1 <D 1^a 0
                            base_step(2),
                            // 10^n 1 B> 1^a+1 0
                            chain_step(0, "a+1"),
                            base_step(2),
                            // 10^n 1^a+1 <D 01
                            chain_step(1, "a+1"),
                            // 10^n <D 1^a+1 0 1
                            induction_step(&[("n", "n"), ("a", "a+1")]),
                        ],
                    },
                },
                // 4: C(a, a) -> C(a+1, a+1)
                //      A0 B1^a B0 C1 D1^a R3(a, a) D0 B0 C0 (A1 E1)^a+1
                Rule {
                    init_config: Config::from_str("0^inf 10^a A> 0 1^a 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 10^a+1 A> 0 1^a+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        base_step(1),
                        // 10^a 1 B> 1^a
                        chain_step(0, "a"),
                        base_step(2),
                        // 10^a 1^a <D 01
                        chain_step(1, "a"),
                        // 10^a <D 1^a 0 1
                        rule_step(3, &[("n", "a"), ("a", "a")]),
                        // <D 1^2a 0 1^a+1
                        base_step(3),
                        // A> 1^2a+2 0 1^a+1
                        chain_step(2, "a+1"),
                    ]),
                },
                // Proof of non-halting
                Rule {
                    init_config: Config::new(),
                    final_config: Config::from_str("0^inf 10^n A> 0 1^n 0^inf").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            induction_step(&[("n", "n")]),
                            // 10^n A> 0 1^n
                            rule_step(4, &[("a", "n")]),
                        ],
                    },
                },
                // Proof of irregularity:
                // C(n, m) for n+m even
                // C(2b+r, 2c+r) -> C(b+c+r+1, 2b+r+1)
                Rule {
                    init_config: Config::from_str("0^inf 10^2b+r A> 0 1^2c+r 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 10^b+c+r+1 A> 0 1^2b+r+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        base_step(1),
                        // 10^2b+r 1 B> 1^a+2c
                        chain_step(0, "2c+r"),
                        base_step(2),
                        // 10^2b+r 1^2c+r <D 01
                        chain_step(1, "2c+r"),
                        // 10^2b+r <D 1^2c+r 0 1
                        rule_step(3, &[("n", "2b+r"), ("a", "2c+r")]),
                        // <D 1^2b+2c+2r 0 1^2b+r+1
                        base_step(3),
                        // A> 1^2b+2c+2r+2 0 1^2b+r+1
                        chain_step(2, "b+c+r+1"),
                    ]),
                },
                // C(n, m) for n+m odd
                // C(2b+r+1, 2c+r) -> Halt
                Rule {
                    init_config: Config::from_str("0^inf 10^2b+r+1 A> 0 1^2c+r 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 10^b+c+r+1 11 Z> 1^2b+r+2 0^inf")
                        .unwrap(),
                    proof: Proof::Simple(vec![
                        base_step(1),
                        // 10^2b+r+1 1 B> 1^a+2c
                        chain_step(0, "2c+r"),
                        base_step(2),
                        // 10^2b+r+1 1^2c+r <D 01
                        chain_step(1, "2c+r"),
                        // 10^2b+r+1 <D 1^2c+r 0 1
                        rule_step(3, &[("n", "2b+r+1"), ("a", "2c+r")]),
                        // <D 1^2b+2c+2r+1 0 1^2b+r+2
                        base_step(3),
                        // A> 1^2b+2c+2r+3 0 1^2b+r+2
                        chain_step(2, "b+c+r+1"),
                        // 10^b+c+r+1 A> 1 0 1^2b+r+2
                        base_step(2),
                    ]),
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[test]
    fn test_62_mxdys_halt_cryptid1() {
        // https://wiki.bbchallenge.org/wiki/1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC
        // Probviously halting BB(6) Cryptid
        // C(a, b, c) = $ 1^2a+1 C> 0^2b 1^c 01 $

        let rule_set = RuleSet {
            tm: TM::from_str("1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA1LD_1RZ0LC").unwrap(),
            rules: vec![
                chain_rule("1^2n <E", "<E 1^2n", 2), // 0
                chain_rule("A> 1^n", "1^n A>", 1),   // 1
                // 2: 0 1^2a+1 C> 0 -> 1^2a+3 A>
                Rule {
                    init_config: Config::from_str("0 1^2a+1 C> 0").unwrap(),
                    final_config: Config::from_str("1^2a+3 A>").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0 1^2a+1 C> 0
                        base_step(2),
                        // 0 1^2a <E 11
                        chain_step(0, "a"),
                        // 0^ <E 1^2a+2
                        base_step(1),
                        chain_step(1, "2a+2"),
                        // 1^2a+3 A>
                    ]),
                },
                // 3: C(a, b+2, c)  ->  C(a+3, b, c)
                Rule {
                    init_config: Config::from_str("0^inf 1^2a+1 C> 0^4n").unwrap(),
                    final_config: Config::from_str("0^inf 1^2a+6n+1 C>").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 0^inf 1^2a+1 C> 0^4
                            rule_step(2, &[("a", "a")]),
                            // 0^inf 1^2a+3 A> 0^3
                            base_step(4),
                            // 0^inf 1^2a+4 <E 01
                            chain_step(0, "a+2"),
                            // 0^inf <E 1^2a+4 01
                            base_step(1),
                            chain_step(1, "2a+4"),
                            // 0^inf 1^2a+5 A> 01
                            base_step(2),
                            // 0^inf 1^2a+7 C>
                            induction_step(&[("a", "a+3")]),
                        ],
                    },
                },
                chain_rule("1^2n <C", "<C 0^2n", 2), // 4
                // 5: C(1, 2b, c+1) -> C(1, 3b+2, c)
                Rule {
                    init_config: Config::from_str("0^inf 1^3 C> 0^4n 1").unwrap(),
                    final_config: Config::from_str("0^inf 1^3 C> 0^6n+4").unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(3, &[("a", "1"), ("n", "n")]),
                        // 0^inf 1^6n+3 C> 1
                        base_step(2),
                        chain_step(4, "3n+1"),
                        // 0^inf <C 0^6n+4
                        base_step(5),
                    ]),
                },
                // 6: C(1, 2b+1, c+2) -> C(1, 3b+4, c)
                Rule {
                    init_config: Config::from_str("0^inf 1^3 C> 0^4n+2 11").unwrap(),
                    final_config: Config::from_str("0^inf 1^3 C> 0^6n+8").unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(3, &[("a", "1"), ("n", "n")]),
                        // 0^inf 1^6n+3 C> 0011
                        rule_step(2, &[("a", "3n+1")]),
                        // 0^inf 1^6n+5 A> 011
                        base_step(4),
                        chain_step(4, "3n+3"),
                        // 0^inf <C 0^6n+8
                        base_step(5),
                    ]),
                },
                // 7: C(1, 2b, 0) -> C(1, 2, 6b+5)
                Rule {
                    init_config: Config::from_str("0^inf 1^3 C> 0^4n 01 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1^3 C> 0^4 1^6n+5 01 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(3, &[("a", "1"), ("n", "n")]),
                        // 0^inf 1^6n+3 C> 01 0^inf
                        rule_step(2, &[("a", "3n+1")]),
                        // 0^inf 1^6n+5 A> 1 0^inf
                        base_step(5),
                        // 0^inf 1^6n+7 <E 01 0^inf
                        chain_step(0, "3n+3"),
                        // 0^inf 1 <E 1^6n+6 01 0^inf
                        base_step(14),
                        // 0^inf 1^3 C> 0^4 1^6n+5 01 0^inf
                    ]),
                },
                // 8: 0^inf 1^2a+1 A> 1 0^inf -> 0^inf 1^3 C> 0^4 1^2a+1 01 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1^2a+1 A> 1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1^3 C> 0^4 1^2a+1 01 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1^2a+1 A> 1 0^inf
                        base_step(5),
                        // 0^inf 1^2a+3 <E 01 0^inf
                        chain_step(0, "a+1"),
                        // 0^inf 1 <E 1^2a+2 01 0^inf
                        base_step(14),
                    ]),
                },
                // 9: C(1, 2b, 0) -> C(1, 2, 6b+5)
                Rule {
                    init_config: Config::from_str("0^inf 1^3 C> 0^4b 01 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1^3 C> 0^4 1^6b+5 01 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(3, &[("a", "1"), ("n", "b")]),
                        // 0^inf 1^6b+3 C> 01 0^inf
                        rule_step(2, &[("a", "3b+1")]),
                        // 0^inf 1^6b+5 A> 1 0^inf
                        rule_step(8, &[("a", "3b+2")]),
                        // 0^inf 1^3 C> 0^4 1^6b+5 01 0^inf
                    ]),
                },
                // 10: C(1, 2b+1, 1) -> C(1, 2, 6b+9)
                Rule {
                    init_config: Config::from_str("0^inf 1^3 C> 0^4b+2 1 01 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1^3 C> 0^4 1^6b+9 01 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(3, &[("a", "1"), ("n", "b")]),
                        // 0^inf 1^6b+3 C> 00101 0^inf
                        rule_step(2, &[("a", "3b+1")]),
                        // 0^inf 1^6b+5 A> 0101 0^inf
                        base_step(2),
                        // 0^inf 1^6b+7 C> 01 0^inf
                        rule_step(2, &[("a", "3b+3")]),
                        // 0^inf 1^6b+9 A> 1 0^inf
                        rule_step(8, &[("a", "3b+4")]),
                        // 0^inf 1^3 C> 0^4 1^6b+9 01 0^inf
                    ]),
                },
                // 11: C(1, 2b+1, 0) -> Halt(6b+7)
                Rule {
                    init_config: Config::from_str("0^inf 1^3 C> 0^4b+2 01").unwrap(),
                    final_config: Config::from_str("0^inf 1^6b+7 Z> 0").unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(3, &[("a", "1"), ("n", "b")]),
                        // 0^inf 1^6b+3 C> 0001 0^inf
                        rule_step(2, &[("a", "3b+1")]),
                        // 0^inf 1^6b+5 A> 001 0^inf
                        base_step(4),
                    ]),
                },
                // Trajectory
                // Start --(43)--> C(1, 2, 5)
                Rule {
                    init_config: Config::new(),
                    final_config: Config::from_str("0^inf 1^3 C> 0^4 1^5 01 0^inf").unwrap(),
                    proof: Proof::Simple(vec![base_step(43)]),
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[test]
    fn test_62_mxdys_halt_cryptid2() {
        // Variation of test_62_halt_cryptid1
        // Probviously halting BB(6) Cryptid
        // C(a, b, c) = $ 1^2a+1 F> 0^2b 1^c 01 $

        let rule_set = RuleSet {
            tm: TM::from_str("1RB1RA_0RC1RF_1LD1RZ_0LE1LE_1RA1LD_1LD0LF").unwrap(),
            rules: vec![
                chain_rule("1^2n <E", "<E 1^2n", 2), // 0
                chain_rule("A> 1^n", "1^n A>", 1),   // 1
                // 2: 0 1^2a+1 C> 0 -> 1^2a+3 A>
                Rule {
                    init_config: Config::from_str("0 1^2a+1 F> 0").unwrap(),
                    final_config: Config::from_str("1^2a+3 A>").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0 1^2a+1 F> 0
                        base_step(2),
                        // 0 1^2a <E 11
                        chain_step(0, "a"),
                        // 0^ <E 1^2a+2
                        base_step(1),
                        chain_step(1, "2a+2"),
                        // 1^2a+3 A>
                    ]),
                },
                // 3: C(a, b+2, c)  ->  C(a+3, b, c)
                Rule {
                    init_config: Config::from_str("0^inf 1^2a+1 F> 0^4n").unwrap(),
                    final_config: Config::from_str("0^inf 1^2a+6n+1 F>").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 0^inf 1^2a+1 F> 0^4
                            rule_step(2, &[("a", "a")]),
                            // 0^inf 1^2a+3 A> 0^3
                            base_step(4),
                            // 0^inf 1^2a+4 <E 01
                            chain_step(0, "a+2"),
                            // 0^inf <E 1^2a+4 01
                            base_step(1),
                            chain_step(1, "2a+4"),
                            // 0^inf 1^2a+5 A> 01
                            base_step(2),
                            // 0^inf 1^2a+7 F>
                            induction_step(&[("a", "a+3")]),
                        ],
                    },
                },
                chain_rule("1^2n <F", "<F 0^2n", 2), // 4
                // 5: C(1, 2b, c+1) -> C(1, 3b+2, c)
                Rule {
                    init_config: Config::from_str("0^inf 1^3 F> 0^4n 1").unwrap(),
                    final_config: Config::from_str("0^inf 1^3 F> 0^6n+4").unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(3, &[("a", "1"), ("n", "n")]),
                        // 0^inf 1^6n+3 F> 1
                        base_step(2),
                        chain_step(4, "3n+1"),
                        // 0^inf <C 0^6n+4
                        base_step(5),
                    ]),
                },
                // 6: C(1, 2b+1, c+2) -> C(1, 3b+4, c)
                Rule {
                    init_config: Config::from_str("0^inf 1^3 F> 0^4n+2 11").unwrap(),
                    final_config: Config::from_str("0^inf 1^3 F> 0^6n+8").unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(3, &[("a", "1"), ("n", "n")]),
                        // 0^inf 1^6n+3 F> 0011
                        rule_step(2, &[("a", "3n+1")]),
                        // 0^inf 1^6n+5 A> 011
                        base_step(4),
                        chain_step(4, "3n+3"),
                        // 0^inf <C 0^6n+8
                        base_step(5),
                    ]),
                },
                // 7: C(1, 2b, 0) -> C(1, 2, 6b+5)
                Rule {
                    init_config: Config::from_str("0^inf 1^3 F> 0^4n 01 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1^3 F> 0^4 1^6n+5 01 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(3, &[("a", "1"), ("n", "n")]),
                        // 0^inf 1^6n+3 F> 01 0^inf
                        rule_step(2, &[("a", "3n+1")]),
                        // 0^inf 1^6n+5 A> 1 0^inf
                        base_step(5),
                        // 0^inf 1^6n+7 <E 01 0^inf
                        chain_step(0, "3n+3"),
                        // 0^inf 1 <E 1^6n+6 01 0^inf
                        base_step(14),
                        // 0^inf 1^3 F> 0^4 1^6n+5 01 0^inf
                    ]),
                },
                // 8: 0^inf 1^2a+1 A> 1 0^inf -> 0^inf 1^3 F> 0^4 1^2a+1 01 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1^2a+1 A> 1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1^3 F> 0^4 1^2a+1 01 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1^2a+1 A> 1 0^inf
                        base_step(5),
                        // 0^inf 1^2a+3 <E 01 0^inf
                        chain_step(0, "a+1"),
                        // 0^inf 1 <E 1^2a+2 01 0^inf
                        base_step(14),
                    ]),
                },
                // 9: C(1, 2b, 0) -> C(1, 2, 6b+5)
                Rule {
                    init_config: Config::from_str("0^inf 1^3 F> 0^4b 01 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1^3 F> 0^4 1^6b+5 01 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(3, &[("a", "1"), ("n", "b")]),
                        // 0^inf 1^6b+3 F> 01 0^inf
                        rule_step(2, &[("a", "3b+1")]),
                        // 0^inf 1^6b+5 A> 1 0^inf
                        rule_step(8, &[("a", "3b+2")]),
                        // 0^inf 1^3 F> 0^4 1^6b+5 01 0^inf
                    ]),
                },
                // 10: C(1, 2b+1, 1) -> C(1, 2, 6b+9)
                Rule {
                    init_config: Config::from_str("0^inf 1^3 F> 0^4b+2 1 01 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1^3 F> 0^4 1^6b+9 01 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(3, &[("a", "1"), ("n", "b")]),
                        // 0^inf 1^6b+3 F> 00101 0^inf
                        rule_step(2, &[("a", "3b+1")]),
                        // 0^inf 1^6b+5 A> 0101 0^inf
                        base_step(2),
                        // 0^inf 1^6b+7 F> 01 0^inf
                        rule_step(2, &[("a", "3b+3")]),
                        // 0^inf 1^6b+9 A> 1 0^inf
                        rule_step(8, &[("a", "3b+4")]),
                        // 0^inf 1^3 F> 0^4 1^6b+9 01 0^inf
                    ]),
                },
                // 11: C(1, 2b+1, 0) -> Halt(6b+7)
                Rule {
                    init_config: Config::from_str("0^inf 1^3 F> 0^4b+2 01").unwrap(),
                    final_config: Config::from_str("0^inf 1^6b+5 1 0 1 Z>").unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(3, &[("a", "1"), ("n", "b")]),
                        // 0^inf 1^6b+3 F> 0001 0^inf
                        rule_step(2, &[("a", "3b+1")]),
                        // 0^inf 1^6b+5 A> 001 0^inf
                        base_step(3),
                    ]),
                },
                // Trajectory
                // Start --(43)--> C(1, 2, 5)
                Rule {
                    init_config: Config::new(),
                    final_config: Config::from_str("0^inf 1^3 F> 0^4 1^5 01 0^inf").unwrap(),
                    proof: Proof::Simple(vec![base_step(43)]),
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[test]
    fn test_62_racheline_halt_cryptid() {
        // https://wiki.bbchallenge.org/wiki/1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA
        // Probviously halting BB(6) Cryptid
        // C(a, b, c) = 0^inf 1011^a 1^b 10^c C> 0^inf
        // C(a, b) = C(a, b, 1) = 0^inf 1011^a 1^b 10 C> 0^inf

        let rule_set = RuleSet {
            tm: TM::from_str("1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_1RZ0RA").unwrap(),
            rules: vec![
                chain_rule("10^n <D 0", "<D 0 10^n", 2),    // 0: D0 E1
                chain_rule("A> 10^n", "10^n A>", 4),        // 1: A1 D0 E0 F1
                chain_rule("01 D> 10^n", "1^2n 01 D>", 8),  // 2: D1 C1 A0 B0 C1 A0 B0 C0
                chain_rule("1 F> 10^2n", "1011^n 1 F>", 4), // 3: F1 A0 B1 E0
                // Tape reparsing rules
                simple_rule("<D 0 1 0", "<D 0 10", 0), // 4
                simple_rule("1 0 A>", "10 A>", 0),     // 5
                // 6: 111 10^n C> 0^5 -> 10^n+4 C>
                Rule {
                    init_config: Config::from_str("111 10^n C> 0^5").unwrap(),
                    final_config: Config::from_str("10^n+4 C>").unwrap(),
                    proof: Proof::Simple(vec![
                        // 111 10^n C> 0^5
                        base_step(3), // C0 D0 E1
                        rule_step(4, &[]),
                        // 111 10^n <D 0 10
                        chain_step(0, "n"),
                        // 111 <D 0 10^n+1
                        base_step(6), // D1 C1 A1 D0 E0 F1
                        rule_step(5, &[]),
                        // 10 A> 10^n+2
                        chain_step(1, "n+2"),
                        // 10^n+3 A>
                        base_step(2), // A0 B0
                    ]),
                },
                // 7: 101 10^n C> 0^5 -> 10^n+4 C>
                Rule {
                    init_config: Config::from_str("101 10^n C> 0^5").unwrap(),
                    final_config: Config::from_str("10^n+4 C>").unwrap(),
                    proof: Proof::Simple(vec![
                        // 101 10^n C> 0^5
                        base_step(3), // C0 D0 E1
                        rule_step(4, &[]),
                        // 101 10^n <D 0 10
                        chain_step(0, "n"),
                        // 101 <D 0 10^n+1
                        base_step(8), // D1 C0 D1 C1 A1 D0 E0 F1
                        rule_step(5, &[]),
                        // 10 A> 10^n+2
                        chain_step(1, "n+2"),
                        // 10^n+3 A>
                        base_step(2), // A0 B0
                    ]),
                },
                // 8: 011 10^n C> 0^2  --> 1^2n+3 10 C>
                Rule {
                    init_config: Config::from_str("011 10^n C> 0^2").unwrap(),
                    final_config: Config::from_str("1^2n+3 10 C>").unwrap(),
                    proof: Proof::Simple(vec![
                        // 011 10^n C> 0^2
                        base_step(3), // C0 D0 E1
                        // 011 10^n <D 0 1
                        chain_step(0, "n"),
                        // 011 <D 0 10^n 1
                        base_step(8), // D1 C1 A0 B0 C1 A0 B0 C0
                        // 11 01 D> 10^n 1
                        chain_step(2, "n"),
                        // 1^2n+2 01 D> 1
                        base_step(7), // D1 C1 A0 B0 C1 A0 B0
                    ]),
                },
                // 9: 001 10^n C> 0^2 --> 1^2n+3 10 C>
                Rule {
                    init_config: Config::from_str("001 10^n C> 0^2").unwrap(),
                    final_config: Config::from_str("1^2n+3 10 C>").unwrap(),
                    proof: Proof::Simple(vec![
                        // 001 10^n C> 0^2
                        base_step(3), // C0 D0 E1
                        // 001 10^n <D 0 1
                        chain_step(0, "n"),
                        // 001 <D 0 10^n 1
                        base_step(2), // D1 C0
                        // 01 D> 10^n+1 1
                        chain_step(2, "n+1"),
                        // 1^2n+2 01 D> 1
                        base_step(7), // D1 C1 A0 B0 C1 A0 B0
                    ]),
                },
                // 10: 00 10^2n+1 C> 0^4 -> 1011^n+1 10^2 C>
                Rule {
                    init_config: Config::from_str("00 10^2n+1 C> 0^4").unwrap(),
                    final_config: Config::from_str("1011^n+1 10^2 C>").unwrap(),
                    proof: Proof::Simple(vec![
                        // 00 10^2n+1 C> 0^4
                        base_step(3), // C0 D0 E1
                        // 00 10^2n+1 <D 0 10 0
                        chain_step(0, "2n+1"),
                        // 00 <D 0 10^2n+2 0
                        base_step(2), // D0 E0
                        // 1 F> 10^2n+3 0
                        chain_step(3, "n+1"),
                        // 1011^n+1 1 F> 100
                        base_step(3), // F1 A0 B0
                    ]),
                },
                // 11: 00 10^2n C> 0^4 -> Halt
                Rule {
                    init_config: Config::from_str("00 10^2n C> 0^4").unwrap(),
                    final_config: Config::from_str("1011^n+1 11 Z>").unwrap(),
                    proof: Proof::Simple(vec![
                        // 00 10^2n C> 0^4
                        base_step(3), // C0 D0 E1
                        rule_step(4, &[]),
                        // 00 10^2n <D 0 10 0
                        chain_step(0, "2n"),
                        // 00 <D 0 10^2n+2 0
                        base_step(2), // D0 E0
                        // 1 F> 10^2n+2 0
                        chain_step(3, "n+1"),
                        // 1011^n+1 1 F> 00
                        base_step(1), // F0
                    ]),
                },
                // 12: C(a, 3n+r, c) --> C(a, r, 4n+c)
                Rule {
                    init_config: Config::from_str("1^3n 10^c C> 0^inf").unwrap(),
                    final_config: Config::from_str("10^4n+c C> 0^inf").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            rule_step(6, &[("n", "c")]),
                            induction_step(&[("n", "n"), ("c", "c+4")]),
                        ],
                    },
                },
                // 13: C(a+1, 3k) --> C(a, 8k+6)
                Rule {
                    init_config: Config::from_str("1011 1^3k 10 C> 0^inf").unwrap(),
                    final_config: Config::from_str("1^8k+6 10 C> 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 1011 1^3k 10 C> 0^inf
                        rule_step(12, &[("n", "k"), ("c", "1")]),
                        // 1011 10^4k+1 C> 0^inf
                        rule_step(8, &[("n", "4k+1")]),
                        // 1^8k+6 10 C>
                    ]),
                },
                // 14: C(a+2, 3k+1) --> C(a, 8k+16)
                Rule {
                    init_config: Config::from_str("1011^2 1^3k+1 10 C> 0^inf").unwrap(),
                    final_config: Config::from_str("1^8k+16 10 C> 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 1011^2 1^3k+1 10 C> 0^inf
                        rule_step(12, &[("n", "k"), ("c", "1")]),
                        // 1011 1011 1 10^4k+1 C> 0^inf
                        rule_step(6, &[("n", "4k+1")]),
                        // 1011 10 10^4k+5 C> 0^inf
                        rule_step(8, &[("n", "4k+6")]),
                        // 1^8k+16 10 C>
                    ]),
                },
                // 15: C(a+2, 3k+2) --> C(a, 8k+22)
                Rule {
                    init_config: Config::from_str("1011^2 1^3k+2 10 C> 0^inf").unwrap(),
                    final_config: Config::from_str("1^8k+22 10 C> 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 1011^2 1^3k+2 10 C> 0^inf
                        rule_step(12, &[("n", "k"), ("c", "1")]),
                        // 1011 1011 11 10^4k+1 C> 0^inf
                        rule_step(6, &[("n", "4k+1")]),
                        // 1011 101 10^4k+5 C> 0^inf
                        rule_step(7, &[("n", "4k+5")]),
                        // 1011 10^4k+9 C> 0^inf
                        rule_step(8, &[("n", "4k+9")]),
                        // 1^8k+22 10 C>
                    ]),
                },
                // 16: C(0, 3k) --> C(2k, 8)
                Rule {
                    init_config: Config::from_str("0^inf 1^3k 10 C> 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1011^2k 1^8 10 C> 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1^3k 10 C> 0^inf
                        rule_step(12, &[("n", "k"), ("c", "1")]),
                        // 0^inf 10^4k+1 C> 0^inf
                        rule_step(10, &[("n", "2k")]),
                        // 1011^2k+1 10^2 C>
                        rule_step(8, &[("n", "2")]),
                        // 1011^2k 1^8 10 C>
                    ]),
                },
                // 17: C(0, 3k+1) --> C(0, 8k+5)
                Rule {
                    init_config: Config::from_str("0^inf 1^3k+1 10 C> 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1^8k+5 10 C> 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1^3k+1 10 C> 0^inf
                        rule_step(12, &[("n", "k"), ("c", "1")]),
                        // 0^inf 1 10^4k+1 C> 0^inf
                        rule_step(9, &[("n", "4k+1")]),
                        // 0^inf 1^8k+5 10 C> 0^inf
                    ]),
                },
                // 18: C(1, 3k+1) --> Halt(6k+14)
                Rule {
                    init_config: Config::from_str("0^inf 1011 1^3k+1 10 C> 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1011^2k+4 11 Z> 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1011 1^3k+1 10 C> 0^inf
                        rule_step(12, &[("n", "k"), ("c", "1")]),
                        // 0^inf 1011 1 10^4k+1 C> 0^inf
                        rule_step(6, &[("n", "4k+1")]),
                        // 0^inf 10 10^4k+5 C> 0^inf
                        rule_step(11, &[("n", "2k+3")]),
                        // 1011^2k+4 11 Z>
                    ]),
                },
                // 19: C(0, 3k+2) --> C(0, 8k+5)
                Rule {
                    init_config: Config::from_str("0^inf 1^3k+2 10 C> 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1^8k+5 10 C> 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1^3k+2 10 C> 0^inf
                        rule_step(12, &[("n", "k"), ("c", "1")]),
                        // 0^inf 11 10^4k+1 C> 0^inf
                        rule_step(8, &[("n", "4k+1")]),
                        // 0^inf 1^8k+5 10 C> 0^inf
                    ]),
                },
                // 20: C(1, 3k+2) --> C(2k+4, 8)
                Rule {
                    init_config: Config::from_str("0^inf 1011 1^3k+2 10 C> 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1011^2k+4 1^8 10 C> 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1011 1^3k+2 10 C> 0^inf
                        rule_step(12, &[("n", "k"), ("c", "1")]),
                        // 0^inf 1011 11 10^4k+1 C> 0^inf
                        rule_step(6, &[("n", "4k+1")]),
                        // 0^inf 101 10^4k+5 C> 0^inf
                        rule_step(7, &[("n", "4k+5")]),
                        // 0^inf 10^4k+9 C> 0^inf
                        // 0^inf 10^4k+1 C> 0^inf
                        rule_step(10, &[("n", "2k+4")]),
                        // 1011^2k+5 10^2 C>
                        rule_step(8, &[("n", "2")]),
                        // 1011^2k+4 1^8 10 C>
                    ]),
                },
                // Initial Trajectory
                // Start --(2)--> C(0, 0) --> C(11_292, 8) --> ...
                Rule {
                    init_config: Config::new(),
                    final_config: Config::from_str("0^inf 1011^11292 1^8 10 C> 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        base_step(2), // A0 B0
                        // C(0, 0): $ 10 C> $
                        rule_step(16, &[("k", "0")]),
                        // C(0, 8)
                        rule_step(19, &[("k", "2")]),
                        // C(0, 21)
                        rule_step(16, &[("k", "7")]),
                        // C(14, 8)
                        rule_step(15, &[("k", "2")]),
                        // C(12, 38)
                        rule_step(15, &[("k", "12")]),
                        // C(10, 118)
                        rule_step(14, &[("k", "39")]),
                        // C(8, 328)
                        rule_step(14, &[("k", "109")]),
                        // C(6, 888)
                        rule_step(13, &[("k", "296")]),
                        // C(5, 2374)
                        rule_step(14, &[("k", "791")]),
                        // C(3, 6344)
                        rule_step(15, &[("k", "2114")]),
                        // C(1, 16934)
                        rule_step(20, &[("k", "5644")]),
                        // C(11292, 8)
                        // Rule 17 not used yet ... it will be used at next reset:
                        //  6_818  C(0, ~10^2_900.82 ≡ 1 (mod 3))
                    ]),
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[test]
    fn test_34_uni() {
        // Analysis of Pavel's 3x4 TM shared 31 May 2023:
        //      https://discord.com/channels/960643023006490684/1095740122139480195/1113545691994783804
        // Common configs:
        //      C(a, b, c, d, e) = $ 1 2^a 1 3^b 1 01^c 1 2^d <A 2^e $
        // Rules:
        //    1)    C(a, b, c,  d+2, 2e+1)  ->  C(a, b, c, d, 2 (e+2) + 1)
        //          C(a, b, c, 2k+r, 2e+1)  ->  C(a, b, c, r, 2 (e+2k) + 1)
        //    2)    C(a, b, c+1, 1, 2e+1)  ->  C(a, b, c, 2e+5, 3)
        //                                 ->  C(a, b, c, 1, 2 (2e+5) + 1)
        //          C(a, b, c, 1, 2e+1)  ->  C(a, b, 0, 1, 2 f(c, e) + 1)
        //              where f(c, e) = rep(λx -> 2x+5, c)(e)  ~= 2^c
        //    3)    C(a, b+1, 0, 1, 2e+1)  ->  C(a, b, e+2, 1, 3)
        //                                 ->  C(a, b, 0, 1, 2 f(e+2, 1) + 1)
        //          C(a, b, 0, 1, 2e+1)  ->  C(a, 0, 0, 1, 2 g(b, e) + 1)
        //              where g(b, e) = rep(λx -> f(x+2, 1), b)(e)  ~= 2^^b
        //    4)    C(a+2, 0, 0, 1, 2e+1)  ->  C(a, 2e+7, 0, 1, 3)
        //                                 ->  C(a, 0, 0, 1, 2 g(2e+7, 1) + 1)
        //          C(2a+r, 0, 0, 1, 2e+1)  ->  C(r, 0, 0, 1, 2 h(a, e) + 1)
        //              where h(a, e) = rep(λx -> g(2x+7, 1), a)(e)  ~= 2^^^a
        //    5)    C(0, 0, 0, 1, 2e+1)  ->  C(0, 0, 0, 1, 2 h(4e+19, g(1, 1)) + 1)

        // f1(x) = 2x+5
        // f2(x, y) = f1^x(y)  ~= 2^x
        fn f2(x: CountExpr, y: CountExpr) -> CountExpr {
            CountExpr::RecursiveExpr(RecursiveExpr {
                func: Box::new(Function {
                    bound_var: "x".parse().unwrap(),
                    expr: "2x+5".parse().unwrap(),
                }),
                num_repeats: Box::new(x),
                base: Box::new(y),
            })
        }
        // f3(x, y) = rep(λz -> f2(z+2, 1), x)(y) ~= 2^^x
        fn f3(x: CountExpr, y: CountExpr) -> CountExpr {
            CountExpr::RecursiveExpr(RecursiveExpr {
                func: Box::new(Function {
                    bound_var: "z".parse().unwrap(),
                    expr: f2("z+2".parse().unwrap(), 1.into()),
                }),
                num_repeats: Box::new(x),
                base: Box::new(y),
            })
        }
        // f4(x, y) = rep(λz -> f3(2z+7, 1), x)(y) ~= 2^^^x
        fn f4(x: CountExpr, y: CountExpr) -> CountExpr {
            CountExpr::RecursiveExpr(RecursiveExpr {
                func: Box::new(Function {
                    bound_var: "z".parse().unwrap(),
                    expr: f3("2z+7".parse().unwrap(), 1.into()),
                }),
                num_repeats: Box::new(x),
                base: Box::new(y),
            })
        }
        // f5(x, y) = ((λz.f4(4z+19, f2(1, 1)))^x y) ~= 2^^^^x
        fn f5(x: CountExpr, y: CountExpr) -> CountExpr {
            CountExpr::RecursiveExpr(RecursiveExpr {
                func: Box::new(Function {
                    bound_var: "z".parse().unwrap(),
                    expr: f4("4z+19".parse().unwrap(), f3(1.into(), 1.into())),
                }),
                num_repeats: Box::new(x),
                base: Box::new(y),
            })
        }

        let rule_set = RuleSet {
            tm: TM::from_str("1RB2LA1RC3RA_1LA2RA2RB0RC_1RZ3LC1RA1RB").unwrap(),
            rules: vec![
                // Level 0: Basic chain rules
                chain_rule("A> 2^2n", "1^2n A>", 2),
                chain_rule("C> 2^2n", "1^2n C>", 2),
                chain_rule("1^n <A", "<A 2^n", 1),
                chain_rule("B> 2^n", "2^n B>", 1),
                chain_rule("1^n <C", "<C 3^n", 1),
                chain_rule("B> 3^2n", "01^n B>", 2),
                chain_rule("A> 3^n", "3^n A>", 1),
                // Level 1: C(a, b, c, 2k+r, 2e+1)  ->  C(a, b, c, r, 2 (e+2k) + 1)
                Rule {
                    init_config: Config::from_str("2^2n <A 2^2e+1 0^inf").unwrap(),
                    final_config: Config::from_str("<A 2^4n+2e+1 0^inf").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 22^n+1 <A 2^2e+1  --(1)-->  22^n 21 C> 2^2e+1
                            base_step(1),
                            // 22^n 21 C> 2^2e+1  -->  22^n 21 11^e C> 2
                            chain_step(1, "e"),
                            // 22^n 21 11^e C> 200  --(3)-->  22^n 21 11^e 11 <A 1
                            base_step(3),
                            // 22^n 2 1^2e+3 <A 1  -->  22^n 2 <A 2^2e+3 1
                            chain_step(2, "2e+3"),
                            // 22^n 2 <A 2^2e+3 1  --(1)-->  22^n 1 C> 2^2e+3 1
                            base_step(1),
                            // 22^n 1 C> 2^2e+3 1  -->  22^n 1 11^e+1 C> 21
                            chain_step(1, "e+1"),
                            // 22^n 1 11^e+1 C> 21  --(3)-->  22^n 1 11^e+1 <A 22
                            base_step(3),
                            // 22^n 1 11^e+1 <A 22  -->  22^n <A 2^2e+5
                            chain_step(2, "2e+3"),
                            // 22^n <A 2^2(e+2)+1  -->  <A 2^2(e+2(n+1))+1
                            induction_step(&[("e", "e+2")]),
                        ],
                    },
                },
                // Level 2: C(a, b, c, 1, 2e+1)  ->  C(a, b, 0, 1, 2 f2(c, e) + 1)
                //   where f2(c, e) = rep(λx -> 2x+5, c)(e)  ~= 2^c
                Rule {
                    init_config: Config::from_str("01^n 1 2 <A 2^2e+1 0^inf").unwrap(),
                    final_config: Config::from_str("1 2 <A 2^2x+1 0^inf")
                        .unwrap()
                        .subst(&VarSubst::single(
                            Variable::from_str("x").unwrap(),
                            f2("n".parse().unwrap(), "e".parse().unwrap()),
                        ))
                        .unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![
                            // Note this requires RecursionExpr comparison supporting equality between:
                            //      2e+1  ==  λx.2x+1 ((λx.2x+5)^0 e)
                        ],
                        proof_inductive: vec![
                            // 01^n+1 12 <A 2^2e+1 00  -->  01^n+1 1 <A 2^2e+3 1
                            base_step(1),
                            chain_step(1, "e"),
                            base_step(3),
                            chain_step(2, "2e+3"),
                            // 01^n+1 1 <A 2^2e+3 1  --(3)-->  01^n 1 B> 22 2^2e+3 1
                            base_step(3),
                            chain_step(3, "2e+5"),
                            // 01^n 1 2^2e+5 B> 100  --(9)-->  01^n 1 2^2e+5 <A 222
                            base_step(9),
                            // Level 1: 01^n 1 2^2(e+2)+1 <A 2^3  -->  01^n 12 <A 2^2(2e+5)+1
                            rule_step(7, &[("n", "e+2"), ("e", "1")]),
                            // Induction: 01^n 12 <A 2^2(2e+5)+1  -->  12 <A 2^2x+1  for x = f2(n, 2e+5) = f2(n+1, e)
                            induction_step(&[("e", "2e+5")]),
                            // Note this requires RecursionExpr comparison supporting equality between:
                            //      λx.2x+1 ((λx.2x+5)^n 2e+5)
                            //      λx.2x+1 ((λx.2x+5)^n+1 e)
                        ],
                    },
                },
                // Level 3: C(a, b, 0, 1, 2e+1)  ->  C(a, 0, 0, 1, 2 f3(b, e) + 1)
                //   where f3(b, e) = rep(λx -> f2(x+2, 1), b)(e)  ~= 2^^b
                Rule {
                    init_config: Config::from_str("3^n 1 1 2 <A 2^2e+1 0^inf").unwrap(),
                    final_config: Config::from_str("1 1 2 <A 2^2x+1 0^inf")
                        .unwrap()
                        .subst(&VarSubst::single(
                            Variable::from_str("x").unwrap(),
                            f3("n".parse().unwrap(), "e".parse().unwrap()),
                        ))
                        .unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 3^n+1 112 <A 2^2e+1 00  -->  3^n+1 <A 2^2e+5 1
                            base_step(1),
                            chain_step(1, "e"),
                            base_step(3),
                            chain_step(2, "2e+5"),
                            // 3^n+1 <A 2^2e+5 1  --(1)-->  3^n 3 A> 2^2e+5 1
                            base_step(1),
                            // 3^n 3 A> 2^2e+5 1  -->  3^n 3 11^e+2 A> 21
                            chain_step(0, "e+2"),
                            base_step(2),
                            chain_step(4, "2e+5"),
                            // 3^n 3 <C 3^2e+6  --(1)-->  3^n 1 B> 3^2e+6
                            base_step(1),
                            // 3^n 1 B> 3^2e+6  -->  3^n 1 01^e+3 B>
                            chain_step(5, "e+3"),
                            // 3^n 1 01^e+3 B> 000  --(13)-->  3^n 1 01^e+2 12 <A 2^3
                            base_step(13),
                            // Level 2: 3^n 1 01^e+2 12 <A 2^3  -->  3^n 112 <A 2^{2 f2(e+2, 1) + 1}
                            rule_step(8, &[("n", "e+2"), ("e", "1")]),
                            // Induction: 3^n 112 <A 2^{2 f1(e+2, 1) + 1}  -->  112 <A 2^2x+1
                            //      for x = f3(n, f2(e+2, 1)) = f3(n+1, e)
                            induction_step_expr(&[(
                                "e".parse().unwrap(),
                                f2("e+2".parse().unwrap(), 1.into()),
                            )]),
                        ],
                    },
                },
                // Level 4: C(2a+r, 0, 0, 1, 2e+1)  ->  C(r, 0, 0, 1, 2 f4(a, e) + 1)
                //   where f4(a, e) = rep(λx -> f3(2x+7), a)(e)  ~= 2^^^a
                Rule {
                    init_config: Config::from_str("2^2n 1 1 1 2 <A 2^2e+1 0^inf").unwrap(),
                    final_config: Config::from_str("1 1 1 2 <A 2^2x+1 0^inf")
                        .unwrap()
                        .subst(&VarSubst::single(
                            Variable::from_str("x").unwrap(),
                            f4("n".parse().unwrap(), "e".parse().unwrap()),
                        ))
                        .unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 2^2n+2 1112 <A 2^2e+1 00  -->  2^2n+2 <A 2^2e+6 1
                            base_step(1),
                            chain_step(1, "e"),
                            base_step(3),
                            chain_step(2, "2e+6"),
                            // 2^2n+2 <A 2^2e+6 1  -->  2^2n+1 1^2e+7 C> 1
                            base_step(1),
                            chain_step(1, "e+3"),
                            // 2^2n+1 1^2e+7 C> 1  -->  2^2n+1 <C 3^2e+8
                            base_step(1),
                            chain_step(4, "2e+7"),
                            // 2^2n+1 <C 3^2e+8  -->  2^n 1 3^2e+8 A>
                            base_step(1),
                            chain_step(6, "2e+8"),
                            // 2^n 1 3^2e+8 A> 00  --(23)-->  2^n 1 3^2e+7 112 <A 2^3
                            base_step(23),
                            // Level 3: 2^n 1 3^2e+7 112 <A 2^3  -->  2^n 112 <A 2^{2 f3(2e+7, 1) + 1}
                            rule_step(9, &[("n", "2e+7"), ("e", "1")]),
                            // Induction: 2^n 112 <A 2^{2 f3(2e+7, 1) + 1}  -->  112 <A 2^2x+1
                            //      for x = f4(n, f3(2e+7, 1)) = f4(n+1, e)
                            induction_step_expr(&[(
                                "e".parse().unwrap(),
                                f3("2e+7".parse().unwrap(), 1.into()),
                            )]),
                        ],
                    },
                },
                // Level 5: C(0, 0, 0, 1, 2e+1)  ->  C(0, 0, 0, 1, 2 f4(4e+19, f3(1, 1)) + 1)
                // Infinite
                Rule {
                    init_config: Config::from_str("0^inf 1 1 1 1 2 <A 2^2e+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1 1 1 1 2 <A 2^2x+1 0^inf")
                        .unwrap()
                        .subst(&VarSubst::single(
                            Variable::from_str("x").unwrap(),
                            f5("n".parse().unwrap(), "e".parse().unwrap()),
                        ))
                        .unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 11112 <A 2^2e+1 00  -->  <A 2^2e+7 1
                            base_step(1),
                            chain_step(1, "e"),
                            base_step(3),
                            chain_step(2, "2e+7"),
                            // 0 <A 2^2e+7 1  -->  1 2^2e+7 B> 1
                            base_step(1),
                            chain_step(3, "2e+7"),
                            // 1 2^2e+7 B> 100  --(9)-->  1 2^2e+7 <A 2^3
                            base_step(9),
                            // Level 1: 12 2^2e+6 <A 2^3  -->  12 <A 2^2(2e+6)+3
                            rule_step(7, &[("n", "e+3"), ("e", "1")]),
                            // 12 <A 2^4e+15 00  -->  <A 2^4e+18 1
                            base_step(1),
                            chain_step(1, "2e+7"),
                            base_step(3),
                            chain_step(2, "4e+18"),
                            // 0 <A 2^4e+18 1  -->  1 2^4e+18 B> 1
                            base_step(1),
                            chain_step(3, "4e+18"),
                            // 1 2^4e+18 B> 100  --(9)-->  1 2^4e+18 <A 2^3
                            base_step(9),
                            // Level 1: 1 2^4e+18 <A 2^3  -->  1 <A 2^2(4e+18)+3
                            rule_step(7, &[("n", "2e+9"), ("e", "1")]),
                            // 01 <A 2^8e+39  -->  1 2^8e+40 B>
                            base_step(2),
                            chain_step(3, "8e+40"),
                            // 1 2^8e+40 B> 0^6  --(30)--> 1 2^8e+38 1 3^1 112 <A 2^3
                            base_step(30),
                            // Level 3: 3^1 112 <A 2^3  -->  112 <A 2^{2 f3(1, 1) + 1}
                            //      f3(1, 1) = f2(3, 1)
                            rule_step(9, &[("n", "1"), ("e", "1")]),
                            // Level 4: 1 2^8e+38 1112 <A 2^{2 f3(1, 1) + 1}  -->  11112 <A 2^2x+1
                            //      for x = f4(4e+19, f3(1, 1))
                            ProofStep::RuleStep {
                                rule_id: 10,
                                var_assignment: VarSubst::from(&[
                                    (
                                        Variable::from_str("n").unwrap(),
                                        CountExpr::from_str("4e+19").unwrap(),
                                    ),
                                    (Variable::from_str("e").unwrap(), f3(1.into(), 1.into())),
                                ]),
                            },
                            induction_step_expr(&[(
                                "e".parse().unwrap(),
                                f4("4e+19".parse().unwrap(), f3(1.into(), 1.into())),
                            )]),
                        ],
                    },
                },
                // Proof that TM is infinite starting from blank tape.
                Rule {
                    init_config: Config::new(),
                    final_config: Config::from_str("0^inf 1 1 1 1 2 <A 2^2x+1 0^inf")
                        .unwrap()
                        .subst(&VarSubst::single(
                            Variable::from_str("x").unwrap(),
                            f5("n".parse().unwrap(), f4(7.into(), f3(1.into(), 1.into()))),
                        ))
                        .unwrap(),
                    proof: Proof::Simple(vec![
                        // <A --> 1 2^14 1 3 112 <A 2^3
                        ProofStep::TMSteps(210),
                        // Level 3: 1 2^14 1 3 112 <A 2^3  -->  1 2^14 1 112 <A 2^{2 f3(1, 1) + 1}
                        ProofStep::RuleStep {
                            rule_id: 9,
                            var_assignment: VarSubst::from(&[
                                ("n".parse().unwrap(), 1.into()),
                                ("e".parse().unwrap(), 1.into()),
                            ]),
                        },
                        // Level 4: 1 2^14 1112 <A 2^{2 f3(1, 1) + 1}  -->  1 112 <A 2^{2 f4(7, f3(1, 1)) + 1}
                        ProofStep::RuleStep {
                            rule_id: 10,
                            var_assignment: VarSubst::from(&[
                                ("n".parse().unwrap(), 7.into()),
                                ("e".parse().unwrap(), f3(1.into(), 1.into())),
                            ]),
                        },
                        // TODO: Apply Level 5
                        ProofStep::RuleStep {
                            rule_id: 11,
                            var_assignment: VarSubst::from(&[
                                ("n".parse().unwrap(), "n".parse().unwrap()),
                                ("e".parse().unwrap(), f4(7.into(), f3(1.into(), 1.into()))),
                            ]),
                        },
                    ]),
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[ignore = "sum expression support needed"]
    #[test]
    fn test_25_dyuan() {
        // @dyuan01's halting 2x5 counter-bouncer.
        //      https://discord.com/channels/960643023006490684/1084047886494470185/1230916624626876529
        // Note: This proof is not complete, there are several Admits.

        let n = Variable::from_str("n").unwrap();
        let a = Variable::from_str("a").unwrap();
        let x = Variable::from_str("x").unwrap();

        // Repeat λx.2x+1 n times starting from 0.
        //   = 2^n - 1
        fn rep2n1(n: &CountExpr) -> CountExpr {
            CountExpr::RecursiveExpr(RecursiveExpr {
                func: Box::new(Function::affine(2, 1)),
                num_repeats: Box::new(n.clone()),
                base: Box::new(0.into()),
            })
        }

        // a_2n1 = a + rep2n1(n) = a + 2^n - 1
        let a_2n1 = CountExpr::from_str("a+x")
            .unwrap()
            .subst(&VarSubst::single(x, rep2n1(&n.into())))
            .unwrap();

        // e6 = 2^6 - 1 = 63
        let e6 = rep2n1(&6.into());
        // e7 = 2^7 - 1 = 127
        // Note: e7 = rep2n1(7) ... but our system cannot detect that equivalence.
        let e7 = CountExpr::from_str("a+x")
            .unwrap()
            .subst(&VarSubst::from(&[
                (a, e6.checked_add(&1.into()).unwrap()),
                (x, e6.clone()),
            ]))
            .unwrap();
        // ee7 = 2^e7 - 1 = 2^127 - 1
        let ee7 = rep2n1(&e7);

        let rule_set = RuleSet {
            tm: TM::from_str("1RB0LB---4RA0LA_2LA3LA3LB0RA2LA").unwrap(),
            rules: vec![
                chain_rule("A> 033^n", "104^n A>", 3),
                chain_rule("104^n <A", "<A 302^n", 5),
                chain_rule("104^n <B", "<B 033^n", 5),
                simple_rule("000 <B", "104 A>", 7),
                // 0^inf 104^a 1104 A> 302^n  -->  0^inf 104^{a + 2^n - 1} 1104 A> 033^n
                Rule {
                    init_config: Config::from_str("0^inf 104^a 1104 A> 302^n").unwrap(),
                    final_config: Config::from_str("0^inf 104^x 1104 A> 033^n")
                        .unwrap()
                        .subst(&VarSubst::single(x, a_2n1.clone()))
                        .unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // First Induction:  0^inf 104^a 1104 A> 302^n+1  -->  0^inf 104^a_2n1 1104 A> 033^n 302
                            induction_step(&[("a", "a")]),
                            // A> 033^n 302  -->  104^n A> 302  -->  104^n <A 033  -->  <A 302^n 033
                            chain_step(0, "n"),
                            base_step(5),
                            chain_step(1, "n"),
                            // 1104 <A  -->  <B 0302
                            base_step(6),
                            // 000 104^a_2n1 <B  -->  000 <B 033^a_2n1  --> 104 A> 033^a_2n1  -->  104 104^a_2n1 A>
                            ProofStep::RuleStep {
                                rule_id: 2,
                                var_assignment: VarSubst::from(&[(n, a_2n1.clone())]),
                            },
                            rule_step(3, &[]),
                            ProofStep::RuleStep {
                                rule_id: 0,
                                var_assignment: VarSubst::from(&[(n, a_2n1.clone())]),
                            },
                            // A> 0302  -->  1104 A>
                            base_step(8),
                            ProofStep::Admit,
                            // Second Induction:  0^inf 104^{a_2n1 + 1}         1104 A> 033^n 302
                            //               -->  0^inf 104^{a_2n1 + 1 + 2n1}   1104 A> 302^n 302
                            ProofStep::InductiveStep(VarSubst::from(&[
                                (n, n.into()),
                                // TODO: Cannot add 1 to a_2n1 (RecursionExpr).
                                // (a, a_2n1 + 1),
                            ])),
                            // TODO: This in order to prove the final config, we must equate:
                            //          λx.a+x ((λn.2n+1)^n+1 1)
                            //          λy.(λz.z+y (λx.a+x ((λn.2n+1)^n 1))) ((λn.2n+1)^n 1)   [+1]
                            // ie:   a + (2^n+1 - 1)  ==  a + (2^n - 1) + (2^n - 1) + 1
                            // One idea to support this would be to expand VarSum to support arbitrary
                            // RecursionExprs, not just simple variables ...
                        ],
                    },
                },
                Rule {
                    init_config: Config::from_str("0^inf 104 104^a 1104 A> 302^n").unwrap(),
                    final_config: Config::from_str("0^inf 104 104^x 1104 A> 033^n")
                        .unwrap()
                        .subst(&VarSubst::single(x, a_2n1.clone()))
                        .unwrap(),
                    proof: Proof::Simple(vec![
                        ProofStep::RuleStep {
                            rule_id: 4,
                            var_assignment: VarSubst::from(&[
                                (a, CountExpr::var_plus(a, 1)),
                                (n, n.into()),
                            ]),
                        },
                        ProofStep::Admit,
                    ]),
                },
                // Halt Proof
                Rule {
                    init_config: Config::new(),
                    final_config: Config::from_str(
                        "0^inf 104^x 1104 104^126 1 Z> 033^7 0302 302 033 3303 02^3 0^inf",
                    )
                    .unwrap()
                    .subst(&VarSubst::single(x, ee7.clone()))
                    .unwrap(),
                    proof: Proof::Simple(vec![
                        base_step(642),
                        // [1104] A> [302]6 [3033] [033]2 [0302] [00] [02] [02]
                        ProofStep::RuleStep {
                            rule_id: 4,
                            var_assignment: VarSubst::from(&[(a, 0.into()), (n, 6.into())]),
                        },
                        // [104]63 [1104] A> [033]6 [3033] [033]2 [0302] [00] [02] [02]
                        base_step(97),
                        // [104]63 <B [0302] [302]6 [0302] [302]2 [3303] [02] [02] [02]
                        ProofStep::RuleStep {
                            rule_id: 2,
                            var_assignment: VarSubst::from(&[(n, e6.clone())]),
                        },
                        rule_step(3, &[]),
                        ProofStep::RuleStep {
                            rule_id: 0,
                            var_assignment: VarSubst::from(&[(n, e6.clone())]),
                        },
                        base_step(8),
                        // [104]64 [1104] A> [302]6 [0302] [302]2 [3303] [02] [02] [02]
                        ProofStep::RuleStep {
                            rule_id: 5,
                            var_assignment: VarSubst::from(&[(a, e6.clone()), (n, 6.into())]),
                        },
                        // [104]127 [1104] A> [033]6 [0302] [302]2 [3303] [02] [02] [02]
                        base_step(73),
                        // [104]127 <A [3033] [033]6 [0302] [033][302] [3303] [02] [02] [02]
                        ProofStep::RuleStep {
                            rule_id: 1,
                            var_assignment: VarSubst::from(&[(n, e7.clone())]),
                        },
                        rule_step(3, &[]),
                        ProofStep::RuleStep {
                            rule_id: 0,
                            var_assignment: VarSubst::from(&[(n, e7.clone())]),
                        },
                        // ...
                        // [1104] A> [302]126 [3033] [033]6 [0302] [033][302] [3303] [02] [02] [02]
                        // ...
                    ]),
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[test]
    fn test_25_t4_dyuan() {
        // 1RB3LA4RB0RB2LA_1LB2LA3LA1RA1RZ
        //   @dyuan01's halting 2x5 counter-bouncer.
        //   https://discord.com/channels/960643023006490684/1084047886494470185/1254826217375273112
        //   Estimated score > (10↑)^4 6.5

        let a = (2_u64.pow(25) - 2_u64.pow(19) - 9) / 3;
        assert!(a == 11010045);
        //let b = (2^(a+27)-2^(a+2)-11)/3;

        let rule_set = RuleSet {
            tm: TM::from_str("1RB3LA4RB0RB2LA_1LB2LA3LA1RA1RZ").unwrap(),
            rules: vec![
                simple_rule("A>", "A>", 0), // Dummy rule so that numbers line up :P
                // Basic Rules
                simple_rule("01 <A", "11 A>", 3),          // 1
                chain_rule("11^n <A", "<A 33^n", 2),       // 2
                chain_rule("A> 33^n", "01^n A>", 2),       // 3
                simple_rule("01 <A 3", "11 0 B>", 4),      // 4
                chain_rule("11^n <A 3", "<A 3 33^n", 2),   // 5
                chain_rule("0 B> 33^n", "01^n 0 B>", 2),   // 6
                simple_rule("A> 21", "<A 22", 3),          // 7
                simple_rule("A> 22", "<A 23", 3),          // 8
                chain_rule("A> 23^n", "41^n A>", 2),       // 9
                simple_rule("A> 0^inf", "<A 21 0^inf", 3), // 10
                simple_rule("0 B> 21", "<A 3 33", 6),      // 11
                simple_rule("0 B> 22 0^inf", "11 1 Z> 1 0^inf", 6), // 12
                chain_rule("0 B> 23^n", "11^n 0 B>", 4),   // 13
                chain_rule("41^n <A", "<A 23^n", 2),       // 14
                simple_rule("0^inf 11 <A", "0^inf 11 0 B>", 5), // 15
                // Counter Rules
                // 16) Counter Rule (A)
                // 01 11^x <A -> 11 01^x A>
                Rule {
                    init_config: Config::from_str("01 11^x <A").unwrap(),
                    final_config: Config::from_str("11 01^x A>").unwrap(),
                    proof: Proof::Simple(vec![
                        chain_step(2, "x"),
                        rule_step(1, &[]),
                        chain_step(3, "x"),
                    ]),
                },
                // 17) Counter Rule (1)
                // 01 11^x <A 23^y 0^inf -> 11 01^x <A 23^y 21 0^inf
                Rule {
                    init_config: Config::from_str("01 11^x <A 23^y 0^inf").unwrap(),
                    final_config: Config::from_str("11 01^x <A 23^y 21 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(16, &[("x", "x")]),
                        chain_step(9, "y"),
                        rule_step(10, &[]),
                        chain_step(14, "y"),
                    ]),
                },
                // 18) Counter Rule (2)
                // 01 11^x <A 23^y 21 -> 11 01^x <A 23^y 22
                Rule {
                    init_config: Config::from_str("01 11^x <A 23^y 21").unwrap(),
                    final_config: Config::from_str("11 01^x <A 23^y 22").unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(16, &[("x", "x")]),
                        chain_step(9, "y"),
                        rule_step(7, &[]),
                        chain_step(14, "y"),
                    ]),
                },
                // 19) Counter Rule (3)
                // 01 11^x <A 23^y 22 -> 11 01^x <A 23^y 23
                Rule {
                    init_config: Config::from_str("01 11^x <A 23^y 22").unwrap(),
                    final_config: Config::from_str("11 01^x <A 23^y+1").unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(16, &[("x", "x")]),
                        chain_step(9, "y"),
                        rule_step(8, &[]),
                        chain_step(14, "y"),
                    ]),
                },
                // 20) Counter Rule (4)
                // 0^inf 11^x+1 <A 3 -> 0^inf 11 01^x 0 B>
                Rule {
                    init_config: Config::from_str("0^inf 11^x+1 <A").unwrap(),
                    final_config: Config::from_str("0^inf 11 01^x 0 B>").unwrap(),
                    proof: Proof::Simple(vec![
                        chain_step(2, "x"),
                        rule_step(15, &[]),
                        chain_step(6, "x"),
                    ]),
                },
                // 21) Counter Rule (5)
                // 01 11^x <A 3 -> 11 01^x 0 B>
                Rule {
                    init_config: Config::from_str("01 11^x <A 3").unwrap(),
                    final_config: Config::from_str("11 01^x 0 B>").unwrap(),
                    proof: Proof::Simple(vec![rule_step(16, &[("x", "x")]), base_step(1)]),
                },
                // Advanced Rules
                // 22) Advanced Rule (1)
                // 01^3 0 B> 0^inf -> 11 01^3 <A 21 0^inf
                simple_rule("01^3 0 B> 0^inf", "11 01^3 <A 21 0^inf", 36),
                // 23) Advanced Rule (2)
                // 01 11^x+2 0 B> 0^inf -> 11 01^x 11^2 01 <A 21 0^inf
                Rule {
                    init_config: Config::from_str("01 11^x+2 0 B> 0^inf").unwrap(),
                    final_config: Config::from_str("11 01^x 11^2 01 <A 21 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        base_step(4),
                        chain_step(2, "x+1"),
                        rule_step(1, &[]),
                        chain_step(3, "x+1"),
                        base_step(25),
                    ]),
                },
                // Overflow Rules
                // 24) Overflow Rule (1)
                // 0^inf 11^x+2 <A 23^y+2 21 0^inf -> 0^inf 11 01^x 11 01^y 11 01^3 <A 21 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 11^x+2 <A 23^y+2 21 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 11 01^x 11 01^y 11 01^3 <A 21 0^inf")
                        .unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(20, &[("x", "x+1")]),
                        chain_step(13, "y+2"),
                        rule_step(11, &[]),
                        rule_step(21, &[("x", "y+2")]),
                        chain_step(6, "1"),
                        rule_step(22, &[]),
                    ]),
                },
                // 25) Overflow Rule (2)
                // 0^inf 11^x+2 <A 23^y+2 0^inf -> 0^inf 11 01^x 11 01^y 11^2 01 <A 21 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 11^x+2 <A 23^y+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 11 01^x 11 01^y 11^2 01 <A 21 0^inf")
                        .unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(20, &[("x", "x+1")]),
                        chain_step(13, "y+2"),
                        rule_step(23, &[("x", "y")]),
                    ]),
                },
                // 26) Overflow Rule (3)
                // 0^inf 11^x+1 <A 23^y+1 22 0^inf -> 0^inf 11 01^x 11^y+2 1 Z> 1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 11^x+1 <A 23^y+1 22 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 11 01^x 11^y+2 1 Z> 1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        rule_step(20, &[("x", "x")]),
                        chain_step(13, "y+1"),
                        rule_step(12, &[]),
                    ]),
                },
                // Halt Proof
                Rule {
                    init_config: Config::new(),
                    final_config: Config::from_str("0^inf 11 01^a+b+c+31 11^d+1 1 Z> 1 0^inf")
                        .unwrap()
                        .subst(&VarSubst::from(&[
                            ("a".parse().unwrap(), a.into()),
                            // ("b".parse().unwrap(), b),
                            // ("c".parse().unwrap(), c),
                            // ("d".parse().unwrap(), d),
                        ]))
                        .unwrap(),
                    proof: Proof::Simple(vec![
                        base_step(2430),
                        // [11]^7 <A [23]^17 [21]
                        rule_step(24, &[("x", "5"), ("y", "15")]),
                        // [11] [01]^5 [11] [01]^15 [11] [01]^3 <A [21]
                        ProofStep::Admit,
                    ]),
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[test]
    fn test_34_a14_uni() {
        // https://www.sligocki.com/2024/05/22/bb-3-4-a14.html
        //   1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC
        //     Discovered by @uni on 25 Apr 2024.
        //     Scores exactly 2{15}5 + 14 = (2 ↑^15 5) + 14 > Ack(14)

        // f(k, x, y) = g_k^x(y)
        //      g_0(y) = y + 1
        //      g_{k+1}(y) = g_k^{2y+2}(0)
        // By some strange coincidence:
        //      2 f(k, x, 0) + 4 = 2{k}(x+2) = 2 ↑^k (x+2)
        fn f(k: CountType, x: CountExpr, y: CountExpr) -> CountExpr {
            match k {
                0 => x,
                k => CountExpr::RecursiveExpr(RecursiveExpr {
                    func: Box::new(Function {
                        bound_var: "z".parse().unwrap(),
                        expr: f(k - 1, "2z+2".parse().unwrap(), 0.into()),
                    }),
                    num_repeats: Box::new(x),
                    base: Box::new(y),
                }),
            }
        }

        // This TM simulates an Ackermann level rule.
        // We cannot prove that rule generally in our system (because it depends on double induction).
        // But we can prove every level of it individually.
        // This function proves each level of the Ackermann rule sequentially and then we use it up to k == 15 below.
        //
        // General rule:
        //      0^inf 3^2e+1 2^k+1 A> 1^n  -->  0^inf 3^2x+1 2^k+1 A>  for x = f(k, n, e)
        // Steps (for e = 0):
        //      t_0(n) ~= 4 n^2
        //      t_k(n) ~= sum_{x=0}^{n-1} t_{k-1}(2 g_k^x(0) + 2)
        //
        //      t_1(n) = sum_{x=0}^{n-1} t_0(2 g_1^x(0) + 2)
        //                ~= sum 4 (2^{x+2} - 2)^2
        //                ~= 16/3 (g_1^n(0))^2
        //
        //      t_2(n) = sum_{x=0}^{n-1} t_1(2 g_2^x(0) + 2)
        //                  ~= sum 16/3 (g_2^{x+1}(0))^2
        //                  ~= 16/3 (g_2^n(0))^2
        //
        //      t_k(n) ~= 16/3 (g_k^n(0))^2
        fn rule_level(k: CountType, prev_rule_id: usize) -> Rule {
            if k < 1 {
                panic!("k must be >= 1");
            }
            Rule {
                init_config: Config::from_str("0^inf 3^2e+1 2^k+1 A> 1^n")
                    .unwrap()
                    .subst(&VarSubst::single("k".parse().unwrap(), k.into()))
                    .unwrap(),
                final_config: Config::from_str("0^inf 3^2x+1 2^k+1 A>")
                    .unwrap()
                    .subst(&VarSubst::from(&[
                        ("k".parse().unwrap(), k.into()),
                        (
                            "x".parse().unwrap(),
                            f(k, "n".parse().unwrap(), "e".parse().unwrap()),
                        ),
                    ]))
                    .unwrap(),

                proof: Proof::Inductive {
                    proof_base: vec![],
                    proof_inductive: vec![
                        // 0^inf 3^2e+1 2^k+1 A> 1^n+1
                        base_step(1),
                        // 0^inf 3^2e+1 2^k+1 <B 3 1^n
                        rule_step(4, &[("a", &k.to_string()), ("n", "2e+1")]),
                        // 0^inf 2^k+1 <B 1^2e+1 3 1^n
                        base_step(2 * k + 2),
                        // 0^inf 3 2^k A> 1^2e+2 3 1^n $
                        rule_step(prev_rule_id, &[("n", "2e+2"), ("e", "0")]),
                        // 0^inf 3^2x+1 2^k A> 3 1^n $
                        base_step(1),
                        // 0^inf 3^2x+1 2^k+1 A> 1^n $
                        induction_step_expr(&[(
                            "e".parse().unwrap(),
                            f(k - 1, "2e+2".parse().unwrap(), 0.into()),
                        )]),
                    ],
                },
            }
        }

        let rule_set = RuleSet {
            tm: TM::from_str("1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC").unwrap(),
            rules: vec![
                chain_rule("2^n <C", "<C 3^n", 1), // 0
                chain_rule("C> 3^n", "2^n C>", 1), // 1
                chain_rule("A> 3^n", "2^n A>", 1), // 2 [Unused]
                chain_rule("B> 1^n", "3^n B>", 1), // 3
                // 4: 3^n 2^a+1 <B  -->  2^a+1 <B 1^n
                //      in n(2a+3) steps
                Rule {
                    init_config: Config::from_str("3^n 2^a+1 <B").unwrap(),
                    final_config: Config::from_str("2^a+1 <B 1^n").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            base_step(1),
                            chain_step(0, "a"),
                            base_step(1),
                            chain_step(1, "a"),
                            base_step(1),
                            induction_step(&[("a", "a")]),
                        ],
                    },
                },
                // 5: B(1, n, e)  -->  B(1, 0, e+n) = B(1, 0, g_0^n(e))
                //      in t_0(n, e) steps
                // Where:
                //      t_0(0, e) = 0
                //      t_0(n, e) = 8e+9 + t_0(n-1, e+1)
                // So,
                //      t_0(n, e) = 4n(n-1) + n(8e+9)
                //      t_0(n, 0) = 4 n^2 + 5n
                Rule {
                    init_config: Config::from_str("0^inf 3^2e+1 2 A> 1^n").unwrap(),
                    final_config: Config::from_str("0^inf 3^2n+2e+1 2 A>").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 0^inf 3^2e+1 2 A> 1^n+1
                            base_step(1),
                            // 0^inf 3^2e+1 2 <B 3 1^n
                            rule_step(4, &[("a", "0"), ("n", "2e+1")]),
                            // 0^inf 2 <B 1^2e+1 3 1^n
                            base_step(2),
                            // 0^inf 3 B> 1^2e+2 3 1^n
                            chain_step(3, "2e+2"),
                            // 0^inf 3^2e+3 B> 3 1^n
                            base_step(1),
                            // 0^inf 3^2e+3 2 A> 1^n
                            induction_step(&[("e", "e+1")]),
                        ],
                    },
                },
                // 15 layers of Ackermann rules
                rule_level(1, 5),   // 6
                rule_level(2, 6),   // 7
                rule_level(3, 7),   // 8
                rule_level(4, 8),   // 9
                rule_level(5, 9),   // 10
                rule_level(6, 10),  // 11
                rule_level(7, 11),  // 12
                rule_level(8, 12),  // 13
                rule_level(9, 13),  // 14
                rule_level(10, 14), // 15
                rule_level(11, 15), // 16
                rule_level(12, 16), // 17
                rule_level(13, 17), // 18
                rule_level(14, 18), // 19
                rule_level(15, 19), // 20
                // Halt Proof
                Rule {
                    init_config: Config::new(),
                    final_config: Config::from_str("0^inf 3^2x+1 2^16 1 Z> 0^inf")
                        .unwrap()
                        .subst(&VarSubst::single(
                            "x".parse().unwrap(),
                            f(15, 3.into(), 0.into()),
                        ))
                        .unwrap(),
                    proof: Proof::Simple(vec![
                        base_step(241),
                        // $ 3 2^16 A> 1^3 2 $
                        rule_step(20, &[("n", "3"), ("e", "0")]),
                        // $ 3^2x+1 2^16 A> 2 $  with x = f(15, 3, 0)
                        base_step(1),
                    ]),
                },
                // Permutation Halt Proof
                // If you start in state B on a blank tape, this leads to a
                // slightly smaller giant score:  2{6}5 + 5
                //      TNF: 1RB3RB1LC2LA_2LA2RB1LB3RA_3LA1RZ1LC2RA
                Rule {
                    init_config: Config::from_str("0^inf B> 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 3^2x+1 2^7 1 Z> 0^inf")
                        .unwrap()
                        .subst(&VarSubst::single(
                            "x".parse().unwrap(),
                            f(6, 3.into(), 0.into()),
                        ))
                        .unwrap(),
                    proof: Proof::Simple(vec![
                        base_step(86),
                        // $ 3 2^7 A> 1^3 2 $
                        rule_step(11, &[("n", "3"), ("e", "0")]),
                        // $ 3^2x+1 2^7 A> 2 $  with x = f(6, 3, 0)
                        base_step(1),
                    ]),
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[test]
    fn test_34_a11_uni() {
        // 1RB1RZ1LA2RB_1RC3RC1LA2LB_2LB2RC1LC3RB
        //      Shared by @uni on 23 May 2024.
        //      Halt(SuperPowers(10))
        //      https://discord.com/channels/960643023006490684/1026577255754903572/1243057809268932620
        //  Score: g_13^2(1) + 14 = 2{12}4 + 11 > Ack(11)

        // Common config: 3 <A 1^b 2^c 0^inf

        // f(k, x, y) = g_k^x(y)
        //      g_1(y) = y + 2
        //      g_{k+1}(y) = g_k^{y+1}(1)
        //
        //  g_1^x(y) = 2x + y
        //
        //  g_k(y) = 2{k-2}(y+3) - 3
        //  g_k^x(1) = g_{k+1}(x-1) = 2{k-1}(x+2) - 3
        fn f(k: CountType, x: CountExpr, y: CountExpr) -> CountExpr {
            match k {
                0 => unreachable!("k must be >= 1"),
                1 => CountExpr::from_str("2x+y")
                    .unwrap()
                    .subst(&VarSubst::from(&[
                        ("x".parse().unwrap(), x.clone()),
                        ("y".parse().unwrap(), y.clone()),
                    ]))
                    .unwrap(),
                k => CountExpr::RecursiveExpr(RecursiveExpr {
                    func: Box::new(Function {
                        bound_var: "z".parse().unwrap(),
                        expr: f(k - 1, "z+1".parse().unwrap(), 1.into()),
                    }),
                    num_repeats: Box::new(x),
                    base: Box::new(y),
                }),
            }
        }

        // Ackermann level rule.
        //
        // General rule:
        //      3^n <A 1^k 2^c 0^inf  -->  <A 1^k 2^x 0^inf  for x = f(k, n, c)
        fn rule_level(k: CountType, prev_rule_id: usize) -> Rule {
            if k < 2 {
                panic!("k must be >= 2");
            }
            Rule {
                init_config: Config::from_str("3^n <A 1^k 2^c 0^inf")
                    .unwrap()
                    .subst(&VarSubst::single("k".parse().unwrap(), k.into()))
                    .unwrap(),
                final_config: Config::from_str("<A 1^k 2^x 0^inf")
                    .unwrap()
                    .subst(&VarSubst::from(&[
                        ("k".parse().unwrap(), k.into()),
                        (
                            "x".parse().unwrap(),
                            f(k, "n".parse().unwrap(), "c".parse().unwrap()),
                        ),
                    ]))
                    .unwrap(),

                proof: Proof::Inductive {
                    proof_base: vec![],
                    proof_inductive: vec![
                        // 3^n+1 <A 1^k 2^c 0^inf
                        base_step(1),
                        // 3^n 2 B> 1^k 2^c 0^inf
                        rule_step(4, &[("b", &(k - 1).to_string()), ("n", "c")]),
                        // 3^n 2 3^c B> 1^k 0^inf
                        base_step(1),
                        // 3^n 2 3^c+1 C> 1^k-1 0^inf
                        chain_step(0, &(k - 1).to_string()),
                        // 3^n 2 3^c+1 2^k-1 C> 0^inf
                        base_step(2),
                        // 3^n 2 3^c+1 2^k-2 <A 12 0^inf
                        chain_step(3, &(k - 2).to_string()),
                        // 3^n 2 3^c+1 <A 1^k-1 2 0^inf
                        rule_step(prev_rule_id, &[("n", "c+1"), ("c", "1")]),
                        // 3^n 2 <A 1^k-1 2^x 0^inf   for x = f(k-1, c+1, 1)
                        base_step(1),
                        // 3^n <A 1^k 2^x 0^inf
                        induction_step_expr(&[(
                            "c".parse().unwrap(),
                            f(k - 1, "c+1".parse().unwrap(), 1.into()),
                        )]),
                        // <A 1^k 2^y 0^inf   for y = f(k, n, x)
                    ],
                },
            }
        }

        let rule_set = RuleSet {
            tm: TM::from_str("1RB1RZ1LA2RB_1RC3RC1LA2LB_2LB2RC1LC3RB").unwrap(),
            rules: vec![
                chain_rule("C> 1^n", "2^n C>", 1), // 0
                chain_rule("2^n <C", "<C 1^n", 1), // 1
                chain_rule("3^n <B", "<B 2^n", 1), // 2
                chain_rule("2^n <A", "<A 1^n", 1), // 3
                // 4
                Rule {
                    init_config: Config::from_str("B> 1^b+1 2^n").unwrap(),
                    final_config: Config::from_str("3^n B> 1^b+1").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // B> 1^b+1 2^n+1
                            base_step(1),
                            // 3 C> 1^b 2^n+1
                            chain_step(0, "b"),
                            // 3 2^b C> 2^n+1
                            base_step(1),
                            // 3 2^b <C 1 2^n
                            chain_step(1, "b"),
                            // 3 <C 1^b+1 2^n
                            base_step(1),
                            // 3 B> 1^b+1 2^n
                            induction_step(&[("b", "b")]),
                        ],
                    },
                },
                // 5
                Rule {
                    init_config: Config::from_str("3^n <A 1 2^c 0^inf").unwrap(),
                    final_config: Config::from_str("<A 1 2^c+2n 0^inf").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 3^n+1 <A 1 2^c 0^inf
                            base_step(1),
                            // 3^n 2 B> 1 2^c 0^inf
                            rule_step(4, &[("b", "0"), ("n", "c")]),
                            // 3^n 2 3^c B> 1 0^inf
                            base_step(2),
                            // 3^n 2 3^c+1 <B 2 0^inf
                            chain_step(2, "c+1"),
                            // 3^n 2 <B 2^c+2 0^inf
                            base_step(1),
                            // 3^n <A 1 2^c+2 0^inf
                            induction_step(&[("c", "c+2")]),
                        ],
                    },
                },
                // Ackermann rules
                rule_level(2, 5),   // 6
                rule_level(3, 6),   // 7
                rule_level(4, 7),   // 8
                rule_level(5, 8),   // 9
                rule_level(6, 9),   // 10
                rule_level(7, 10),  // 11
                rule_level(8, 11),  // 12
                rule_level(9, 12),  // 13
                rule_level(10, 13), // 14
                rule_level(11, 14), // 15
                rule_level(12, 15), // 16
                rule_level(13, 16), // 17
                // Halt Proof
                Rule {
                    init_config: Config::new(),
                    final_config: Config::from_str("0^inf 1 Z> 1^13 2^x 0^inf")
                        .unwrap()
                        .subst(&VarSubst::single(
                            "x".parse().unwrap(),
                            f(13, 2.into(), 1.into()),
                        ))
                        .unwrap(),
                    proof: Proof::Simple(vec![
                        base_step(182),
                        // 0^inf 1 3^2 <A 1^13 2 0^inf
                        rule_step(17, &[("n", "2"), ("c", "1")]),
                        // 0^inf 1 <A 1^13 2^x 0^inf   for x = f(13, 2, 1)
                        base_step(1),
                    ]),
                },
                // Permutation: Start State B.
                //      TNF: 1RB3RB1LC2LA_2LA2RB1LB3RA_1RA1RZ1LC2RA
                //      Score: g_7^2(1) + 8 = 2{6}4 + 5
                Rule {
                    init_config: Config::from_str("0^inf B> 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1 Z> 1^7 2^x 0^inf")
                        .unwrap()
                        .subst(&VarSubst::single(
                            "x".parse().unwrap(),
                            f(7, 2.into(), 1.into()),
                        ))
                        .unwrap(),
                    proof: Proof::Simple(vec![
                        base_step(84),
                        // 0^inf 1 3^2 <A 1^7 2 0^inf
                        rule_step(11, &[("n", "2"), ("c", "1")]),
                        // 0^inf 1 <A 1^7 2^x 0^inf   for x = f(7, 2, 1)
                        base_step(1),
                    ]),
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[test]
    fn test_43_a2_uni() {
        // 1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD
        // SuperPowers(2)
        // Common config: 21^n 2^k <D 1^a 0^inf
        // Note: This proof is not complete, there are several Admits.

        fn f1(n: CountExpr, a: CountExpr) -> CountExpr {
            CountExpr::RecursiveExpr(RecursiveExpr {
                func: Box::new(Function {
                    bound_var: "z".parse().unwrap(),
                    expr: CountExpr::from_str("2z+4").unwrap(),
                }),
                num_repeats: Box::new(n),
                base: Box::new(a),
            })
        }
        fn f2(n: CountExpr, a: CountExpr) -> CountExpr {
            CountExpr::RecursiveExpr(RecursiveExpr {
                func: Box::new(Function {
                    bound_var: "z".parse().unwrap(),
                    expr: f1("z+2".parse().unwrap(), 2.into()),
                }),
                num_repeats: Box::new(n),
                base: Box::new(a),
            })
        }
        fn f3(n: CountExpr, a: CountExpr) -> CountExpr {
            CountExpr::RecursiveExpr(RecursiveExpr {
                func: Box::new(Function {
                    bound_var: "z".parse().unwrap(),
                    expr: f1(1.into(), f2("z+2".parse().unwrap(), 2.into())),
                }),
                num_repeats: Box::new(n),
                base: Box::new(a),
            })
        }

        let rule_set = RuleSet {
            tm: TM::from_str("1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD").unwrap(),
            rules: vec![
                chain_rule("A> 1^2n", "12^n A>", 2), // 0
                chain_rule("12^n <A", "<A 1^2n", 2), // 1
                // 2
                Rule {
                    init_config: Config::from_str("12^n <C 1^2a+1 0^inf").unwrap(),
                    final_config: Config::from_str("<C 1^2a+1+4n 0^inf").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 12^n 12 <C 1^2a+1 0^inf
                            base_step(2),
                            // 12^n 2 A> 1^2a+2 0^inf
                            chain_step(0, "a+1"),
                            // 12^n 2 12^a+1 A> 0^inf
                            base_step(5),
                            // 12^n 2 12^a+1 <A 1^2 0^inf
                            chain_step(1, "a+1"),
                            // 12^n 2 <A 1^2a+4 0^inf
                            base_step(1),
                            // 12^n <C 1^2a+5 0^inf
                            induction_step(&[("a", "a+2")]),
                        ],
                    },
                },
                // 3
                Rule {
                    init_config: Config::from_str("12^n <D 1^2a+2 0^inf").unwrap(),
                    final_config: Config::from_str("<D 1^2x+2 0^inf")
                        .unwrap()
                        .subst(&VarSubst::from(&[(
                            "x".parse().unwrap(),
                            f1("n".parse().unwrap(), "a".parse().unwrap()),
                        )]))
                        .unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 12 <D 1^2a+2 0^inf
                            base_step(2),
                            // 12 2 A> 1^2a+1 0^inf
                            chain_step(0, "a"),
                            // 12 2 12^a A> 1 0^inf
                            base_step(7),
                            // 12 2 12^a <A 1^2 2 0^inf
                            chain_step(1, "a"),
                            // 12 2 <A 1^2a+2 2 0^inf
                            base_step(3),
                            // 2 A> 1^2a+4 2 0^inf
                            chain_step(0, "a+2"),
                            // 2 12^a+2 A> 2 0^inf
                            base_step(1),
                            // 2 12^a+2 <C 1 0^inf
                            rule_step(2, &[("n", "a+2"), ("a", "0")]),
                            // 2 <C 1^4a+9 0^inf
                            base_step(1),
                            // <D 1^4a+10 0^inf
                            induction_step(&[("a", "2a+4")]),
                        ],
                    },
                },
                // 4
                Rule {
                    init_config: Config::from_str("12^n 2 <D 1^2a+2 0^inf").unwrap(),
                    final_config: Config::from_str("2 <D 1^2x+2 0^inf")
                        .unwrap()
                        .subst(&VarSubst::from(&[(
                            "x".parse().unwrap(),
                            f2("n".parse().unwrap(), "a".parse().unwrap()),
                        )]))
                        .unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 122 <D 1^2a+2 0^inf
                            base_step(2),
                            // 1222 A> 1^2a+1 0^inf
                            chain_step(0, "a"),
                            // 1222 12^a A> 1 0^inf
                            base_step(7),
                            // 1222 12^a <A 1^2 2 0^inf
                            chain_step(1, "a"),
                            // 1222 <A 1^2a+2 2 0^inf
                            base_step(4),
                            // 122 A> 1^2a+3 2 0^inf
                            chain_step(0, "a+1"),
                            // 122 12^a+1 A> 12 0^inf
                            base_step(7),
                            // 122 12^a+1 <A 1^2 22 0^inf
                            chain_step(1, "a+1"),
                            // 122 <A 1^2a+4 22 0^inf
                            base_step(3),
                            // 2 A> 1^2a+6 22 0^inf
                            chain_step(0, "a+3"),
                            // 2 12^a+3 A> 22 0^inf
                            base_step(19),
                            // 2 12^a+2 <D 1^6 0^inf
                            rule_step(3, &[("n", "a+2"), ("a", "2")]),
                            // 2 <D 1^2x+2 0^inf   for x = f1(a+2, 2)
                            induction_step_expr(&[(
                                "a".parse().unwrap(),
                                f1("a+2".parse().unwrap(), 2.into()),
                            )]),
                        ],
                    },
                },
                // 5
                Rule {
                    init_config: Config::from_str("0^inf 1^6n <D 1^2a+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf <D 1^2x+2 0^inf")
                        .unwrap()
                        .subst(&VarSubst::from(&[(
                            "x".parse().unwrap(),
                            f3("n".parse().unwrap(), "a".parse().unwrap()),
                        )]))
                        .unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 1^6 <D 1^2a+2 0^inf
                            base_step(1),
                            // 1^4 12 A> 1^2a+2 0^inf
                            chain_step(0, "a+1"),
                            // 1^4 12^a+2 A> 0^inf
                            base_step(5),
                            // 1^4 12^a+2 <A 1^2 0^inf
                            chain_step(1, "a+1"),
                            // 1^4 12 <A 1^2a+4 0^inf
                            base_step(4),
                            // 1^3 12 A> 1^2a+5 0^inf
                            chain_step(0, "a+2"),
                            // 1^3 12^a+3 A> 1 0^inf
                            base_step(7),
                            // 1^3 12^a+3 <A 1^2 2 0^inf
                            chain_step(1, "a+2"),
                            // 1^3 12 <A 1^2a+6 2 0^inf
                            base_step(4),
                            // 1^2 12 A> 1^2a+7 2 0^inf
                            chain_step(0, "a+3"),
                            // 1^2 12^a+4 A> 12 0^inf
                            base_step(7),
                            // 1^2 12^a+4 <A 11 22 0^inf
                            chain_step(1, "a+3"),
                            // 1^2 12 <A 1^2a+8 22 0^inf
                            base_step(4),
                            // 1 12 A> 1^2a+9 22 0^inf
                            chain_step(0, "a+4"),
                            // 1 12^a+5 A> 122 0^inf
                            base_step(30),
                            // 1 12^a+5 2 <D 1^6 0^inf
                            ProofStep::Admit,
                            // This doesn't work yet, b/c the tape actually looks like:
                            //      0^inf 1^6n+2 2 12^a+4 2 <D 1^6 0^inf
                            // which cannot (yet) be normalized to:
                            //      0^inf 1^6n+1 12^a+5 2 <D 1^6 0^inf
                            rule_step(4, &[("n", "a+5"), ("a", "2")]),
                            // 12 <D 1^2x+2 0^inf  x = f2(a+5, 2)
                            ProofStep::RuleStep {
                                rule_id: 3,
                                var_assignment: VarSubst::from(&[
                                    ("n".parse().unwrap(), 1.into()),
                                    ("a".parse().unwrap(), f2("a+5".parse().unwrap(), 2.into())),
                                ]),
                            },
                            // <D 1^2y+2 0^inf  y = f1(1, x) = 2x+4
                        ],
                    },
                },
                chain_rule("B> 1^n", "1^n B>", 1), // 6
                // 7
                Rule {
                    init_config: Config::from_str("0^inf 11 <D 1^2a+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1^2a+2 <D 1^2x+2 0^inf")
                        .unwrap()
                        .subst(&VarSubst::from(&[(
                            "x".parse().unwrap(),
                            f1(1.into(), f2(3.into(), 2.into())),
                        )]))
                        .unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 11 <D 1^2a+2 0^inf
                        base_step(1),
                        // 0^inf 12 A> 1^2a+2 0^inf
                        chain_step(0, "a+1"),
                        // 0^inf 12^a+2 A> 0^inf
                        base_step(5),
                        // 0^inf 12^a+2 <A 1^2 0^inf
                        chain_step(1, "a+1"),
                        // 0^inf 12 <A 1^2a+4 0^inf
                        base_step(3),
                        // 0^inf 1 B> 1^2a+6 0^inf
                        chain_step(6, "2a+6"),
                        // 0^inf 1 1^2a+6 B> 0^inf
                        base_step(66),
                        // 0^inf 1^2a+3 12^3 2 <D 1^6 0^inf
                        rule_step(4, &[("n", "3"), ("a", "2")]),
                        // 0^inf 1^2a+3 2 <D 1^2x+2 0^inf  x = f2(3, 2)
                        ProofStep::RuleStep {
                            rule_id: 3,
                            var_assignment: VarSubst::from(&[
                                ("n".parse().unwrap(), 1.into()),
                                ("a".parse().unwrap(), f2(3.into(), 2.into())),
                            ]),
                        },
                        // 0^inf 1^2a+2 <D 1^2y+2 0^inf  y = f1(1, x) = 2x+4
                    ]),
                },
                // 8
                Rule {
                    init_config: Config::from_str("0^inf 111 <D 1^2a+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1^2a+4 <D 1^2x+2 0^inf")
                        .unwrap()
                        .subst(&VarSubst::from(&[(
                            "x".parse().unwrap(),
                            f1(1.into(), f2(3.into(), 2.into())),
                        )]))
                        .unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 111 <D 1^2a+2 0^inf
                        base_step(1),
                        // 0^inf 1 12 A> 1^2a+2 0^inf
                        chain_step(0, "a+1"),
                        // 0^inf 1 12^a+2 A> 0^inf
                        base_step(5),
                        // 0^inf 1 12^a+2 <A 1^2 0^inf
                        chain_step(1, "a+1"),
                        // 0^inf 112 <A 1^2a+4 0^inf
                        base_step(4),
                        // 0^inf 12 A> 1^2a+5 0^inf
                        chain_step(0, "a+2"),
                        // 0^inf 12^a+3 A> 1 0^inf
                        base_step(7),
                        // 0^inf 12^a+3 <A 1^2 2 0^inf
                        chain_step(1, "a+2"),
                        // 0^inf 12 <A 1^2a+6 2 0^inf
                        base_step(3),
                        // 0^inf 1 B> 1^2a+8 2 0^inf
                        chain_step(6, "2a+8"),
                        // 0^inf 1 1^2a+8 B> 2 0^inf
                        base_step(64),
                        // 0^inf 1^2a+5 12^3 2 <D 1^6 0^inf
                        rule_step(4, &[("n", "3"), ("a", "2")]),
                        // 0^inf 1^2a+5 2 <D 1^2x+2 0^inf  x = f2(3, 2)
                        ProofStep::RuleStep {
                            rule_id: 3,
                            var_assignment: VarSubst::from(&[
                                ("n".parse().unwrap(), 1.into()),
                                ("a".parse().unwrap(), f2(3.into(), 2.into())),
                            ]),
                        },
                        // 0^inf 1^2a+4 <D 1^2y+2 0^inf  y = f1(1, x) = 2x+4
                    ]),
                },
                // Halt Proof
                Rule {
                    init_config: Config::new(),
                    final_config: Config::from_str("0^inf Z> 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        base_step(92),
                        // 0^inf 1^4 12^2 2 <D 1^6 0^inf
                        rule_step(4, &[("n", "2"), ("a", "2")]),
                        // 0^inf 1^4 2 <D 1^2x+2 0^inf  x = f2(2, 2)
                        ProofStep::RuleStep {
                            rule_id: 3,
                            var_assignment: VarSubst::from(&[
                                ("n".parse().unwrap(), 1.into()),
                                ("a".parse().unwrap(), f2(2.into(), 2.into())),
                            ]),
                        },
                        // 0^inf 1^3 <D 1^2y+2 0^inf    y = f1(1, x) = 2x+4
                        ProofStep::RuleStep {
                            rule_id: 8,
                            var_assignment: VarSubst::from(&[(
                                "a".parse().unwrap(),
                                f1(1.into(), f2(2.into(), 2.into())),
                            )]),
                        },
                        // 0^inf 1^4x+12 <D 1^2a+2 0^inf    a = f1(1, f2(3, 2))
                        //
                        ProofStep::Admit, // TODO
                        //
                        // At this point we need to calculate the remainder of
                        // 4x+12 % 6 where x = f2(2, 2) = f1(f1(4, 2)+2, 2)
                        //                   = f1(6 2^2 - 2, 2) = f1(22, 2)
                        //                   = 6 2^22 - 4
                        // so x % 6 = 2 and 4x+12 % 6 = 2
                        // ... but we cannot yet prove this in our system ...
                        //
                        // TODO: In this case this number can fit in memory,
                        // so we could implement a way to evaluate functions ...
                        //
                        // Longer term, we will want to create a way to get
                        // remainders even for formulas that cannot be evaluated.
                        ProofStep::RuleStep {
                            rule_id: 5,
                            var_assignment: VarSubst::from(&[(
                                "n".parse().unwrap(),
                                (2_u64.pow(24) + 1).into(),
                            )]),
                        },
                        // 0^inf 1^2 <D 1^2b+2 0^inf    b = f3(2^24 + 1, a)
                        ProofStep::RuleStep {
                            rule_id: 7,
                            var_assignment: VarSubst::from(&[(
                                "a".parse().unwrap(),
                                f3(
                                    (2_u64.pow(24) + 1).into(),
                                    f1(1.into(), f2(3.into(), 2.into())),
                                ),
                            )]),
                        },
                        // 0^inf 1^2b+2 <D 1^2a+2 0^inf
                    ]),
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }

    #[test]
    fn test_62_1() {
        // 1RB0LB_0LC0RB_0RE1LD_1LA---_1RF0RF_0RA0LE
        // 0^inf D> 0^inf = 1RB---_1LC0RC_0RD0LC_0LE1RA_1LF0LF_0LB0RE
        // 0^inf E> 0^inf = 1RB0RB_0RC0LA_1RD0LD_0LE0RD_0RA1LF_1LC---
        // Let A(a, b, c) = 0^inf 1100101 B> 10^4a+4 0 10^4b+2 001100 10^c+34 0^inf
        // Let B(a, b, c) = 0^inf 1100101 B> 10^4a+4 0 10^2b+34 0 10^2 0 10^c+1 0^inf

        fn a(a: &str, b: &str, c: &str) -> Config {
            Config::from_str("0^inf 1100101 B> 10^4a+4 0 10^4b+2 001100 10^c+34 0^inf")
                .unwrap()
                .subst(&load_vars(&[("a", a), ("b", b), ("c", c)]))
                .unwrap()
        }
        fn b(a: &str, b: &str, c: &str) -> Config {
            Config::from_str("0^inf 1100101 B> 10^4a+4 0 10^2b+34 0 10^2 0 10^c+1 0^inf")
                .unwrap()
                .subst(&load_vars(&[("a", a), ("b", b), ("c", c)]))
                .unwrap()
        }

        #[rustfmt::skip]
        let rule_set = RuleSet {
            tm: TM::from_str("1RB0LB_0LC0RB_0RE1LD_1LA---_1RF0RF_0RA0LE").unwrap(),
            rules: vec![
                chain_rule("B> 10^2n", "0001^n B>", 8),                  // 0
                chain_rule("0001^n 010 <B 0", "010 <B 0 10^2n", 66),     // 1
                chain_rule("0001^n 01010 <B 0", "01010 <B 0 10^2n", 72), // 2
                // 3: B> 10^a+2 0^inf  -->  01010 <B 0 10^a+1 0^inf
                Rule {
                    init_config: Config::from_str("B> 10^a+2 0^inf").unwrap(),
                    final_config: Config::from_str("01010 <B 0 10^a+1 0^inf").unwrap(),
                    proof: Proof::ModularCases {
                        var: "a".parse().unwrap(),
                        proof_cases: vec![
                            vec![
                                // B> 10^2a+2 0^inf
                                chain_step(0, "a+1"),
                                base_step(20),
                                // 0001^a 01010 <B 01 0^inf
                                chain_step(2, "a"),
                                // 01010 <B 0 10^2a+1 0^inf
                            ],
                            vec![
                                // B> 10^2a+3 0^inf
                                chain_step(0, "a+1"),
                                base_step(78),
                                // 0001^a 01010 <B 0 10^2 0^inf
                                chain_step(2, "a"),
                                // 01010 <B 0 10^2a+2 0^inf
                            ],
                        ],
                    },
                },
                // 4: 010 B> 10^2a+3 01  -->  011100101 B> 10^2a+1
                Rule {
                    init_config: Config::from_str("010 B> 10^2a+3 01").unwrap(),
                    final_config: Config::from_str("011100101 B> 10^2a+1").unwrap(),
                    proof: Proof::Simple(vec![
                        // 010 B> 10^2a+3 01
                        chain_step(0, "a+1"),
                        base_step(6),
                        // 010 0001^a+1 010 <B 0
                        chain_step(1, "a+1"),
                        base_step(22),
                        // 011100101 B> 10^2a+1
                    ]),
                },
                // 5: 011100101 B> 10^2a+1 01  -->  1100101 B> 10^2a+3
                Rule {
                    init_config: Config::from_str("011100101 B> 10^2a+1 01").unwrap(),
                    final_config: Config::from_str("1100101 B> 10^2a+3").unwrap(),
                    proof: Proof::Simple(vec![
                        // 011100101 B> 10^2a+1 01
                        chain_step(0, "a"),
                        base_step(6),
                        // 011100101 0001^a 010 <B 0
                        chain_step(1, "a"),
                        base_step(146),
                        // 1100101 B> 10^2a+3
                    ]),
                },
                // 6: 00011100101 B> 10^2a+1 01  -->  001100101 B> 10^2a+3
                Rule {
                    init_config: Config::from_str("00011100101 B> 10^2a+1 01").unwrap(),
                    final_config: Config::from_str("001100101 B> 10^2a+3").unwrap(),
                    proof: Proof::Simple(vec![
                        // 00011100101 B> 10^2a+1 01
                        chain_step(0, "a"),
                        base_step(6),
                        // 00011100101 0001^a 010 <B 0
                        chain_step(1, "a"),
                        base_step(146),
                        // 001100101 B> 10^2a+3
                    ]),
                },
                // 7: 001100101 B> 10^2a+1 01  -->  010 <B 0100 10^2a+3
                Rule {
                    init_config: Config::from_str("001100101 B> 10^2a+1 01").unwrap(),
                    final_config: Config::from_str("010 <B 0100 10^2a+3").unwrap(),
                    proof: Proof::Simple(vec![
                        // 001100101 B> 10^2a+1 01
                        chain_step(0, "a"),
                        base_step(6),
                        // 001100101 0001^a 010 <B 0
                        chain_step(1, "a"),
                        base_step(107),
                        // 010 <B 0100 10^2a+3
                    ]),
                },
                // 8: 0^inf 1100101 B> 10^a+2 0^inf  -->  0^inf 1100101 B> 10^8 0 10^a 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^a+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^a 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^a+2 0^inf
                        rule_step(3, &[("a", "a")]),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^a 0^inf
                    ]),
                },
                // 9: 0^inf 1100101 B> 10^2a+2 0 10^b+1 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a 0 10^b+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^b+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a 0 10^b+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^b+1 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^b+2 0^inf
                        rule_step(3, &[("a", "b")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 01010 <B 0100 10^b+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a 0 10^b+1 0^inf
                    ]),
                },
                // 10: 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^c+4n  -->  0^inf 1100101 B> 10^2a+4n+4 0 10^2b+4n+2 0 10^c
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^c+4n").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+4n+4 0 10^2b+4n+2 0 10^c").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^c+4n+4
                            chain_step(0, "a+2"),
                            base_step(5),
                            // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 0 10^c+4n+4
                            rule_step(4, &[("a", "b")]),
                            rule_step(5, &[("a", "b")]),
                            rule_step(6, &[("a", "b+1")]),
                            rule_step(7, &[("a", "b+2")]),
                            // 0^inf 1100101 0001^a 010 <B 0100 10^2b+7 0 10^c+4n
                            chain_step(1, "a"),
                            base_step(186),
                            // 0^inf 1100101 B> 10^2a+5 0 10^2b+7 0 10^c+4n
                            chain_step(0, "a+2"),
                            base_step(6),
                            // 0^inf 1100101 0001^a+2 010 <B 00 10^2b+6 0 10^c+4n
                            chain_step(1, "a+2"),
                            base_step(186),
                            // 0^inf 1100101 B> 10^2a+8 0 10^2b+6 0 10^c+4n
                            induction_step(&[("a", "a+2"), ("b", "b+2"), ("c", "c")]),
                            // 0^inf 1100101 B> 10^2a+4n+8 0 10^2b+4n+6 0 10^c
                        ],
                    },
                },
                // 11: 0^inf 1100101 B> 10^2a+2 0 10^2b+2 0 10^2 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+2 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+2 0 10^2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+2 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+2 0 10^2 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+3 0 10^2 0^inf
                        rule_step(4, &[("a", "b")]),
                        rule_step(5, &[("a", "b")]),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+3 0^inf
                        rule_step(3, &[("a", "2b+1")]),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+2 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+2 0^inf
                    ]),
                },
                // 12: 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^c+2 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+c+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^c+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+c+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^c+2 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+1 1100 10^c+2 0^inf
                        chain_step(0, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 010 0001^b 010 <B 0 10^c+3 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+c+2 0^inf
                        rule_step(3, &[("a", "2b+c")]),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b+c+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+c+1 0^inf
                    ]),
                },
                // 13: 0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^2c 1100 10^d+2 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+2 01100 10^2c+d+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^2c 1100 10^d+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+2 01100 10^2c+d+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^2c 1100 10^d+2 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+2 0 10^2c 1100 10^d+2 0^inf
                        chain_step(0, "b+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 010 B> 10^2c+1 1100 10^d+2 0^inf
                        chain_step(0, "c"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 <B 0 10^d+3 0^inf
                        chain_step(1, "c"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 B> 10^2c+d+2 0^inf
                        rule_step(3, &[("a", "2c+d")]),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 0001^b 01010 <B 0 10^2 01100 10^2c+d+1 0^inf
                        chain_step(2, "b"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 01010 <B 0100 10^2b+2 01100 10^2c+d+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+2 01100 10^2c+d+1 0^inf
                    ]),
                },
                // 14: 0^inf 1100101 B> 10^2a+2 0 10^2b 001100 10^c+3 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^3 0 10^c+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b 001100 10^c+3 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^3 0 10^c+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b 001100 10^c+3 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+1 001100 10^c+3 0^inf
                        chain_step(0, "b"),
                        base_step(24),
                        // 0^inf 1100101 0001^a 010 0001^b 0101100101 B> 10^c+2 0^inf
                        rule_step(3, &[("a", "c")]),
                        base_step(234),
                        // 0^inf 1100101 0001^a 010 0001^b 11001010001010 B> 10^c+2 0^inf
                        rule_step(3, &[("a", "c")]),
                        base_step(120),
                        // 0^inf 1100101 0001^a 010 0001^b 010 <B 0 10^2 01100 10^3 0 10^c+1 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+1 01100 10^3 0 10^c+1 0^inf
                        rule_step(5, &[("a", "b")]),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+4 0 10^3 0 10^c+1 0^inf
                        chain_step(0, "b+2"),
                        base_step(26),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 0100001010 B> 10^c+2 0^inf
                        rule_step(3, &[("a", "c")]),
                        base_step(90),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 01010 <B 0100 10^3 0 10^c+1 0^inf
                        chain_step(2, "b+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+3 0 10^3 0 10^c+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^3 0 10^c+1 0^inf
                    ]),
                },
                // 15: 0^inf 1100101 B> 10^2a+4 0 10^2b 1100 10^2c+1 0 10^2 1  -->  0^inf 1100101 B> 10^2a+8 0 10^2b+2c+6
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b 1100 10^2c+1 0 10^2 1").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+8 0 10^2b+2c+6").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b 1100 10^2c+1 0 10^2 1
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+1 1100 10^2c+1 0 10^2 1
                        chain_step(0, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a+1 010 0001^b 010 <B 0 10^2c+2 0 10^2 1
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a+1 011100101 B> 10^2b+2c+1 0 10^2 1
                        rule_step(5, &[("a", "b+c")]),
                        rule_step(6, &[("a", "b+c+1")]),
                        rule_step(7, &[("a", "b+c+2")]),
                        // 0^inf 1100101 0001^a 010 <B 0100 10^2b+2c+7
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+5 0 10^2b+2c+7
                        chain_step(0, "a+2"),
                        base_step(6),
                        // 0^inf 1100101 0001^a+2 010 <B 00 10^2b+2c+6
                        chain_step(1, "a+2"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+8 0 10^2b+2c+6
                    ]),
                },
                // 16: 0^inf 1100101 B> 10^2a+2 0 10^2b 00 10^c+2 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a 0 10^2b 1100 10^c+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b 00 10^c+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a 0 10^2b 1100 10^c+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b 00 10^c+2 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+1 00 10^c+2 0^inf
                        chain_step(0, "b"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 010 0001^b 0101 B> 10^c+2 0^inf
                        rule_step(3, &[("a", "c")]),
                        base_step(4),
                        // 0^inf 1100101 0001^a 010 0001^b 01010 <B 01100 10^c+1 0^inf
                        chain_step(2, "b"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 01010 <B 0100 10^2b 1100 10^c+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a 0 10^2b 1100 10^c+1 0^inf
                    ]),
                },
                // 17: 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^2 1100 10^c+1 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+5 0 10^c+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^2 1100 10^c+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+5 0 10^c+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^2 1100 10^c+1 0^inf
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 0 10^2 1100 10^c+1 0^inf
                        rule_step(4, &[("a", "b")]),
                        rule_step(5, &[("a", "b")]),
                        rule_step(6, &[("a", "b+1")]),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+6 0 10^c+1 0^inf
                        chain_step(0, "b+3"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 010 B> 10^c+2 0^inf
                        rule_step(3, &[("a", "c")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 01010 <B 0100 10^c+1 0^inf
                        chain_step(2, "b+2"),
                        base_step(165),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^4 0 10^2b+5 0 10^c+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+5 0 10^c+1 0^inf
                    ]),
                },
                // 18: 0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^2c+1 0 10^d+1 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+1 0 10^2c+1 0 10^d+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^2c+1 0 10^d+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+1 0 10^2c+1 0 10^d+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^2c+1 0 10^d+1 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+2 0 10^2c+1 0 10^d+1 0^inf
                        chain_step(0, "b+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 010 B> 10^2c+2 0 10^d+1 0^inf
                        chain_step(0, "c+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 B> 10^d+2 0^inf
                        rule_step(3, &[("a", "d")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 01010 <B 0100 10^d+1 0^inf
                        chain_step(2, "c"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 01010 <B 0100 10^2c+1 0 10^d+1 0^inf
                        chain_step(2, "b"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 01010 <B 0100 10^2b+1 0 10^2c+1 0 10^d+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+1 0 10^2c+1 0 10^d+1 0^inf
                    ]),
                },
                // 19: 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 0 10^2c+1 01  -->  0^inf 1100101 B> 10^2a+8 0 10^2b+6 1100 10^2c
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 0 10^2c+1 01").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+8 0 10^2b+6 1100 10^2c").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 0 10^2c+1 01
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 0 10^3 0 10^2c+1 01
                        rule_step(4, &[("a", "b")]),
                        rule_step(5, &[("a", "b")]),
                        rule_step(6, &[("a", "b+1")]),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+5 00 10^2c+1 01
                        chain_step(0, "b+2"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 0101 B> 10^2c+1 01
                        chain_step(0, "c"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 0101 0001^c 010 <B 0
                        chain_step(1, "c"),
                        base_step(4),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 010 <B 01100 10^2c
                        chain_step(1, "b+2"),
                        base_step(107),
                        // 0^inf 1100101 0001^a 010 <B 0100 10^2b+7 1100 10^2c
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+5 0 10^2b+7 1100 10^2c
                        chain_step(0, "a+2"),
                        base_step(6),
                        // 0^inf 1100101 0001^a+2 010 <B 00 10^2b+6 1100 10^2c
                        chain_step(1, "a+2"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+8 0 10^2b+6 1100 10^2c
                    ]),
                },
                // 20: 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+2 0 10^d+1 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2c+1 0 10^d+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+2 0 10^d+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2c+1 0 10^d+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+2 0 10^d+1 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+1 1100 10^2c+2 0 10^d+1 0^inf
                        chain_step(0, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 010 0001^b 010 <B 0 10^2c+3 0 10^d+1 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2c+2 0 10^d+1 0^inf
                        chain_step(0, "b+c+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b+c 010 B> 10^d+2 0^inf
                        rule_step(3, &[("a", "d")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b+c 01010 <B 0100 10^d+1 0^inf
                        chain_step(2, "b+c"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b+2c+1 0 10^d+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2c+1 0 10^d+1 0^inf
                    ]),
                },
                // 21: 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^d+4 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+1 0 10^2c+7 0 10^d+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^d+4 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+1 0 10^2c+7 0 10^d+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^d+4 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+6 01100 10^2c+1 0 10^d+4 0^inf
                        chain_step(0, "b+3"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b+2 011100101 B> 10^2c+1 0 10^d+4 0^inf
                        rule_step(5, &[("a", "c")]),
                        rule_step(6, &[("a", "c+1")]),
                        rule_step(7, &[("a", "c+2")]),
                        // 0^inf 1100101 0001^a 010 0001^b+1 010 <B 0100 10^2c+7 0 10^d+1 0^inf
                        chain_step(1, "b+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b 0 10^2c+7 01^d+1 0^inf
                        chain_step(0, "b+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 B> 10^2c+8 0 10^d+1 0^inf
                        chain_step(0, "c+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 010 B> 10^d+2 0^inf
                        rule_step(3, &[("a", "d")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 01010 <B 0100 10^d+1 0^inf
                        chain_step(2, "c+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b 01010 <B 0100 10^2c+7 0 10^d+1 0^inf
                        chain_step(2, "b"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b+1 0 10^2c+7 0 10^d+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+1 0 10^2c+7 0 10^d+1 0^inf
                    ]),
                },
                // 22: 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+7 01 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+1 0 10^2c+8 01100 10^2d+2 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+7 01 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+1 0 10^2c+8 01100 10^2d+2 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+7 01 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+6 01100 10^2c+1 0 10^2d+7 01 0^inf
                        chain_step(0, "b+3"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b+2 011100101 B> 10^2c+1 0 10^2d+7 01 0^inf
                        rule_step(5, &[("a", "c")]),
                        rule_step(6, &[("a", "c+1")]),
                        rule_step(7, &[("a", "c+2")]),
                        // 0^inf 1100101 0001^a 010 0001^b+1 010 <B 0100 10^2c+7 0 10^2d+4 01 0^inf
                        chain_step(1, "b+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2 0 10^2c+7 0 10^2d+4 01 0^inf
                        chain_step(0, "b+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 B> 10^2c+8 0 10^2d+4 01 0^inf
                        chain_step(0, "c+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 010 B> 10^2d+5 01 0^inf
                        rule_step(4, &[("a", "d+1")]),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 011100101 B> 10^2d+3 0^inf
                        rule_step(3, &[("a", "2d+1")]),
                        base_step(39),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 01010 <B 0 10^2 01100 10^2d+2 0^inf
                        chain_step(2, "c+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b 01010 <B 0100 10^2c+8 01100 10^2d+2 0^inf
                        chain_step(2, "b"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b+1 0 10^2c+8 01100 10^2d+2 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+1 0 10^2c+8 01100 10^2d+2 0^inf
                    ]),
                },
                // 23: 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+4 01100 10^e+2 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+1 0 10^2c+7 0 10^2d+2 01100 10^e+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+4 01100 10^e+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+1 0 10^2c+7 0 10^2d+2 01100 10^e+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+4 01100 10^e+2 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+6 01100 10^2c+1 0 10^2d+4 01100 10^e+2 0^inf
                        chain_step(0, "b+3"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b+2 011100101 B> 10^2c+1 0 10^2d+4 01100 10^e+2 0^inf
                        rule_step(5, &[("a", "c")]),
                        rule_step(6, &[("a", "c+1")]),
                        rule_step(7, &[("a", "c+2")]),
                        // 0^inf 1100101 0001^a 010 0001^b+1 010 <B 0100 10^2c+7 0 10^2d+1 01100 10^e+2 0^inf
                        chain_step(1, "b+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2 0 10^2c+7 0 10^2d+1 01100 10^e+2 0^inf
                        chain_step(0, "b+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 B> 10^2c+8 0 10^2d+1 01100 10^e+2 0^inf
                        chain_step(0, "c+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 010 B> 10^2d+2 01100 10^e+2 0^inf
                        chain_step(0, "d+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 010 0001^d 011100101 B> 10^e+2 0^inf
                        rule_step(3, &[("a", "e")]),
                        base_step(39),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 010 0001^d 01010 <B 0 10^2 01100 10^e+1 0^inf
                        chain_step(2, "d"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 01010 <B 0100 10^2d+2 01100 10^e+1 0^inf
                        chain_step(2, "c+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b 01010 <B 0100 10^2c+7 0 10^2d+2 01100 10^e+1 0^inf
                        chain_step(2, "b"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b+1 0 10^2c+7 0 10^2d+2 01100 10^e+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+1 0 10^2c+7 0 10^2d+2 01100 10^e+1 0^inf
                    ]),
                },
                // 24: 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+5 0 10^2e+6 01100 10^f+1 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 01100 10^2c+3 0 10^2d+8 01100 10^2e+1 0 10^f+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+5 0 10^2e+6 01100 10^f+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 01100 10^2c+3 0 10^2d+8 01100 10^2e+1 0 10^f+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+5 0 10^2e+6 01100 10^f+1 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+6 01100 10^2c+1 0 10^2d+5 0 10^2e+6 01100 10^f+1 0^inf
                        chain_step(0, "b+3"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b+2 011100101 B> 10^2c+1 0 10^2d+5 0 10^2e+6 01100 10^f+1 0^inf
                        rule_step(5, &[("a", "c")]),
                        rule_step(6, &[("a", "c+1")]),
                        rule_step(7, &[("a", "c+2")]),
                        // 0^inf 1100101 0001^a 010 0001^b+1 010 <B 0100 10^2c+7 0 10^2d+2 0 10^2e+6 01100 10^f+1 0^inf
                        chain_step(1, "b+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2 0 10^2c+7 0 10^2d+2 0 10^2e+6 01100 10^f+1 0^inf
                        chain_step(0, "b+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 B> 10^2c+8 0 10^2d+2 0 10^2e+6 01100 10^f+1 0^inf
                        chain_step(0, "c+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 010 B> 10^2d+3 0 10^2e+6 01100 10^f+1 0^inf
                        rule_step(4, &[("a", "d")]),
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        rule_step(7, &[("a", "d+2")]),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+2 010 <B 0100 10^2d+7 0 10^2e+2 01100 10^f+1 0^inf
                        chain_step(1, "c+2"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 B> 10^2c+4 0 10^2d+7 0 10^2e+2 01100 10^f+1 0^inf
                        chain_step(0, "c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 010 B> 10^2d+8 0 10^2e+2 01100 10^f+1 0^inf
                        chain_step(0, "d+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 010 0001^d+3 010 B> 10^2e+3 01100 10^f+1 0^inf
                        chain_step(0, "e+1"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 010 0001^d+3 010 0001^e+1 010 <B 0100 10^f+1 0^inf
                        chain_step(1, "e+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 010 0001^d+3 011100101 B> 10^2e+2 0 10^f+1 0^inf
                        chain_step(0, "e+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 010 0001^d+3 011100101 0001^e 010 B> 10^f+2 0^inf
                        rule_step(3, &[("a", "f")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 010 0001^d+3 011100101 0001^e 01010 <B 0100 10^f+1 0^inf
                        chain_step(2, "e"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 010 0001^d+3 01010 <B 0 10^2 01100 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "d+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 01010 <B 0100 10^2d+8 01100 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 011100101 0001^b 01010 <B 0 10^2 01100 10^2c+3 0 10^2d+8 01100 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "b"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b+2 01100 10^2c+3 0 10^2d+8 01100 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 01100 10^2c+3 0 10^2d+8 01100 10^2e+1 0 10^f+1 0^inf
                    ]),
                },
                // 25: 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+4 01100 10^2d+1 0 10^2e+8 01100 10^2f+1 0 10^g+4 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+4 01100 10^2d+7 0 10^2e+1 0 10^2f+7 0 10^g+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+4 01100 10^2d+1 0 10^2e+8 01100 10^2f+1 0 10^g+4 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+4 01100 10^2d+7 0 10^2e+1 0 10^2f+7 0 10^g+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+4 01100 10^2d+1 0 10^2e+8 01100 10^2f+1 0 10^g+4 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+2 01100 10^2c+4 01100 10^2d+1 0 10^2e+8 01100 10^2f+1 0 10^g+4 0^inf
                        chain_step(0, "b+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 B> 10^2c+4 01100 10^2d+1 0 10^2e+8 01100 10^2f+1 0 10^g+4 0^inf
                        chain_step(0, "c+2"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 0001^c+1 011100101 B> 10^2d+1 0 10^2e+8 01100 10^2f+1 0 10^g+4 0^inf
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        rule_step(7, &[("a", "d+2")]),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 0001^c 010 <B 0100 10^2d+7 0 10^2e+5 01100 10^2f+1 0 10^g+4 0^inf
                        chain_step(1, "c"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 B> 10^2c+4 0 10^2d+7 0 10^2e+5 01100 10^2f+1 0 10^g+4 0^inf
                        chain_step(0, "c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 B> 10^2d+8 0 10^2e+5 01100 10^2f+1 0 10^g+4 0^inf
                        chain_step(0, "d+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+3 010 B> 10^2e+6 01100 10^2f+1 0 10^g+4 0^inf
                        chain_step(0, "e+3"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+3 010 0001^e+2 011100101 B> 10^2f+1 0 10^g+4 0^inf
                        rule_step(5, &[("a", "f")]),
                        rule_step(6, &[("a", "f+1")]),
                        rule_step(7, &[("a", "f+2")]),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+3 010 0001^e+1 010 <B 0100 10^2f+7 0 10^g+1 0^inf
                        chain_step(1, "e+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+3 011100101 B> 10^2e+2 0 10^2f+7 0 10^g+1 0^inf
                        chain_step(0, "e+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+3 011100101 0001^e 010 B> 10^2f+8 0 10^g+1 0^inf
                        chain_step(0, "f+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+3 011100101 0001^e 010 0001^f+3 010 B> 10^g+2 0^inf
                        rule_step(3, &[("a", "g")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+3 011100101 0001^e 010 0001^f+3 01010 <B 0100 10^g+1 0^inf
                        chain_step(2, "f+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+3 011100101 0001^e 01010 <B 0100 10^2f+7 0 10^g+1 0^inf
                        chain_step(2, "e"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+3 01010 <B 0 10^2 01100 10^2e+1 0 10^2f+7 0 10^g+1 0^inf
                        chain_step(2, "d+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 01010 <B 0100 10^2d+8 01100 10^2e+1 0 10^2f+7 0 10^g+1 0^inf
                        chain_step(2, "c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 0001^b 010 <B 0 10^2 01100 10^2c+3 0 10^2d+8 01100 10^2e+1 0 10^2f+7 0 10^g+1 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+1 01100 10^2c+3 0 10^2d+8 01100 10^2e+1 0 10^2f+7 0 10^g+1 0^inf
                        rule_step(5, &[("a", "b")]),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+4 0 10^2c+3 0 10^2d+8 01100 10^2e+1 0 10^2f+7 0 10^g+1 0^inf
                        chain_step(0, "b+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 B> 10^2c+4 0 10^2d+8 01100 10^2e+1 0 10^2f+7 0 10^g+1 0^inf
                        chain_step(0, "c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 010 B> 10^2d+9 01100 10^2e+1 0 10^2f+7 0 10^g+1 0^inf
                        rule_step(4, &[("a", "d+3")]),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 011100101 B> 10^2d+8 0 10^2e+1 0 10^2f+7 0 10^g+1 0^inf
                        chain_step(0, "d+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 011100101 0001^d+3 010 B> 10^2e+2 0 10^2f+7 0 10^g+1 0^inf
                        chain_step(0, "e+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 011100101 0001^d+3 010 0001^e 010 B> 10^2f+8 0 10^g+1 0^inf
                        chain_step(0, "f+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 011100101 0001^d+3 010 0001^e 010 0001^f+3 010 B> 10^g+2 0^inf
                        rule_step(3, &[("a", "g")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 011100101 0001^d+3 010 0001^e 010 0001^f+3 01010 <B 0100 10^g+1 0^inf
                        chain_step(2, "f+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 011100101 0001^d+3 010 0001^e 01010 <B 0100 10^2f+7 0 10^g+1 0^inf
                        chain_step(2, "e"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 011100101 0001^d+3 01010 <B 0100 10^2e+1 0 10^2f+7 0 10^g+1 0^inf
                        chain_step(2, "d+3"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 01010 <B 0 10^2 01100 10^2d+7 0 10^2e+1 0 10^2f+7 0 10^g+1 0^inf
                        chain_step(2, "c+1"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 01010 <B 0100 10^2c+4 01100 10^2d+7 0 10^2e+1 0 10^2f+7 0 10^g+1 0^inf
                        chain_step(2, "b+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+3 0 10^2c+4 01100 10^2d+7 0 10^2e+1 0 10^2f+7 0 10^g+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+4 01100 10^2d+7 0 10^2e+1 0 10^2f+7 0 10^g+1 0^inf
                    ]),
                },
                // 26: 0^inf 1100101 B> 10^2a+4 0 10^2b+2 01001100 10^2c+3 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+7 0 10^3 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b+2 01001100 10^2c+3 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+7 0 10^3 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b+2 01001100 10^2c+3 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 01001100 10^2c+3 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        rule_step(4, &[("a", "b")]),
                        // 0^inf 1100101 0001^a+1 011100101 B> 10^2b+1 001100 10^2c+3 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "b"),
                        base_step(24),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 0101100101 B> 10^2c+2 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "c+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 0101100101 0001^c 010 B> 10^2d+2 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "d+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 0101100101 0001^c 010 0001^d 010 B> 10^2e+2 0 10^f+1 0^inf
                        chain_step(0, "e+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 0101100101 0001^c 010 0001^d 010 0001^e 010 B> 10^f+2 0^inf
                        rule_step(3, &[("a", "f")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 0101100101 0001^c 010 0001^d 010 0001^e 01010 <B 0100 10^f+1 0^inf
                        chain_step(2, "e"),
                        base_step(9),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 0101100101 0001^c 010 0001^d 01010 <B 0100 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "d"),
                        base_step(9),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 0101100101 0001^c 01010 <B 0100 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "c"),
                        base_step(234),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 11001010001010 B> 10^2c+2 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "c+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 11001010001010 0001^c 010 B> 10^2d+2 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "d+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 11001010001010 0001^c 010 0001^d 010 B> 10^2e+2 0 10^f+1 0^inf
                        chain_step(0, "e+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 11001010001010 0001^c 010 0001^d 010 0001^e 010 B> 10^f+2 0^inf
                        rule_step(3, &[("a", "f")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 11001010001010 0001^c 010 0001^d 010 0001^e 01010 <B 0100 10^f+1 0^inf
                        chain_step(2, "e"),
                        base_step(9),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 11001010001010 0001^c 010 0001^d 01010 <B 0100 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "d"),
                        base_step(9),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 11001010001010 0001^c 01010 <B 0100 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "c"),
                        base_step(120),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 010 <B 0 10^2 01100 10^3 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a+1 1100101 B> 10^2b+5 01100 10^3 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        rule_step(6, &[("a", "b+2")]),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+8 0 10^3 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "b+4"),
                        base_step(26),
                        // 0^inf 1100101 0001^a 001100101 0001^b+3 0100001010 B> 10^2c+2 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "c+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 001100101 0001^b+3 0100001010 0001^c 010 B> 10^2d+2 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "d+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 001100101 0001^b+3 0100001010 0001^c 010 0001^d 010 B> 10^2e+2 0 10^f+1 0^inf
                        chain_step(0, "e+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 001100101 0001^b+3 0100001010 0001^c 010 0001^d 010 0001^e 010 B> 10^f+2 0^inf
                        rule_step(3, &[("a", "f")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 001100101 0001^b+3 0100001010 0001^c 010 0001^d 010 0001^e 01010 <B 0100 10^f+1 0^inf
                        chain_step(2, "e"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 001100101 0001^b+3 0100001010 0001^c 010 0001^d 01010 <B 0100 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "d"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 001100101 0001^b+3 0100001010 0001^c 01010 <B 0100 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "c"),
                        base_step(90),
                        // 0^inf 1100101 0001^a 001100101 0001^b+3 01010 <B 0100 10^3 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "b+3"),
                        base_step(165),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^4 0 10^2b+7 0 10^3 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+7 0 10^3 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                    ]),
                },
                // 27: 0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+2 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(0, "b+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 010 B> 10^2c+2 0 10^2d+1 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(0, "c+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 B> 10^2d+2 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(0, "d+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 0001^d 010 B> 10^2e+2 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(0, "e+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 0001^d 010 0001^e 010 B> 10^2f+2 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(0, "f+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 0001^d 010 0001^e 010 0001^f 010 B> 10^2g+2 0 10^h+1 0^inf
                        chain_step(0, "g+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 0001^d 010 0001^e 010 0001^f 010 0001^g 010 B> 10^h+2 0^inf
                        rule_step(3, &[("a", "h")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 0001^d 010 0001^e 010 0001^f 010 0001^g 01010 <B 0100 10^h+1 0^inf
                        chain_step(2, "g"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 0001^d 010 0001^e 010 0001^f 01010 <B 0100 10^2g+1 0 10^h+1 0^inf
                        chain_step(2, "f"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 0001^d 010 0001^e 01010 <B 0100 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(2, "e"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 0001^d 01010 <B 0100 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(2, "d"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 01010 <B 0100 10^2d+1 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(2, "c"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 01010 <B 0100 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(2, "b"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 01010 <B 0100 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                    ]),
                },
                // 28: 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2d+2 0 10^2e+5 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+3 0 10^2d+7 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2d+2 0 10^2e+5 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+3 0 10^2d+7 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2d+2 0 10^2e+5 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+1 1100 10^2c+4 0 10^2d+2 0 10^2e+5 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(0, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 010 0001^b 010 <B 0 10^2c+5 0 10^2d+2 0 10^2e+5 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2c+4 0 10^2d+2 0 10^2e+5 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(0, "b+c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b+c+1 010 B> 10^2d+3 0 10^2e+5 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        rule_step(4, &[("a", "d")]),
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        rule_step(7, &[("a", "d+2")]),
                        // 0^inf 1100101 0001^a 011100101 0001^b+c 010 <B 0100 10^2d+7 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(1, "b+c"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+2c+4 0 10^2d+7 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(0, "b+c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 B> 10^2d+8 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(0, "d+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 0001^d+3 010 B> 10^2e+2 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(0, "e+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 0001^d+3 010 0001^e 010 B> 10^2f+2 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(0, "f+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 0001^d+3 010 0001^e 010 0001^f 010 B> 10^2g+2 0 10^h+1 0^inf
                        chain_step(0, "g+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 0001^d+3 010 0001^e 010 0001^f 010 0001^g 010 B> 10^h+2 0^inf
                        rule_step(3, &[("a", "h")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 0001^d+3 010 0001^e 010 0001^f 010 0001^g 01010 <B 0100 10^h+1 0^inf
                        chain_step(2, "g"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 0001^d+3 010 0001^e 010 0001^f 01010 <B 0100 10^2g+1 0 10^h+1 0^inf
                        chain_step(2, "f"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 0001^d+3 010 0001^e 01010 <B 0100 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(2, "e"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 0001^d+3 01010 <B 0100 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(2, "d+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 01010 <B 0100 10^2d+7 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(2, "b+c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+2c+3 0 10^2d+7 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+3 0 10^2d+7 0 10^2e+1 0 10^2f+1 0 10^2g+1 0 10^h+1 0^inf
                    ]),
                },
                // 29: 0^inf 1100101 B> 10^2a+4 0 10^2b+2 00 10^2c+1 0 10^2d+3 0 10^2e+5 0 10^f+1 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+2c+3 0 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b+2 00 10^2c+1 0 10^2d+3 0 10^2e+5 0 10^f+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+2c+3 0 10^2d+7 0 10^2e+1 0 10^f+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b+2 00 10^2c+1 0 10^2d+3 0 10^2e+5 0 10^f+1 0^inf
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 00 10^2c+1 0 10^2d+3 0 10^2e+5 0 10^f+1 0^inf
                        chain_step(0, "b+1"),
                        base_step(6),
                        // 0^inf 1100101 0001^a+1 010 0001^b+1 0101 B> 10^2c+1 0 10^2d+3 0 10^2e+5 0 10^f+1 0^inf
                        chain_step(0, "c"),
                        base_step(6),
                        // 0^inf 1100101 0001^a+1 010 0001^b+1 0101 0001^c 010 <B 00 10^2d+2 0 10^2e+5 0 10^f+1 0^inf
                        chain_step(1, "c"),
                        base_step(4),
                        // 0^inf 1100101 0001^a+1 010 0001^b+1 010 <B 01100 10^2c 0 10^2d+2 0 10^2e+5 0 10^f+1 0^inf
                        chain_step(1, "b+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a+1 011100101 B> 10^2b+1 1100 10^2c 0 10^2d+2 0 10^2e+5 0 10^f+1 0^inf
                        chain_step(0, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 010 <B 0 10^2c+1 0 10^2d+2 0 10^2e+5 0 10^f+1 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a+1 1100101 B> 10^2b+2c+4 0 10^2d+2 0 10^2e+5 0 10^f+1 0^inf
                        chain_step(0, "b+c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 1100101 0001^b+c+1 010 B> 10^2d+3 0 10^2e+5 0 10^f+1 0^inf
                        rule_step(4, &[("a", "d")]),
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        rule_step(7, &[("a", "d+2")]),
                        // 0^inf 1100101 0001^a+1 1100101 0001^b+c 010 <B 0100 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(1, "b+c"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+2c+4 0 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "b+c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 001100101 0001^b+c+1 010 B> 10^2d+8 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "d+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 001100101 0001^b+c+1 010 0001^d+3 010 B> 10^2e+2 0 10^f+1 0^inf
                        chain_step(0, "e+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 001100101 0001^b+c+1 010 0001^d+3 010 0001^e 010 B> 10^f+2 0^inf
                        rule_step(3, &[("a", "f")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 001100101 0001^b+c+1 010 0001^d+3 010 0001^e 01010 <B 0100 10^f+1 0^inf
                        chain_step(2, "e"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 001100101 0001^b+c+1 010 0001^d+3 01010 <B 0100 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "d+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 001100101 0001^b+c+1 01010 <B 0100 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "b+c+1"),
                        base_step(165),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^4 0 10^2b+2c+3 0 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+2c+3 0 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                    ]),
                },
                // 30: 0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+2 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "b+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 010 B> 10^2c+2 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "c+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 B> 10^2d+2 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "d+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 0001^d 010 B> 10^2e+2 0 10^f+1 0^inf
                        chain_step(0, "e+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 0001^d 010 0001^e 010 B> 10^f+2 0^inf
                        rule_step(3, &[("a", "f")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 0001^d 010 0001^e 01010 <B 0100 10^f+1 0^inf
                        chain_step(2, "e"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 0001^d 01010 <B 0100 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "d"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 01010 <B 0100 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "c"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 01010 <B 0100 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "b"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 01010 <B 0100 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^2e+1 0 10^f+1 0^inf
                    ]),
                },
                // 31: 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2d+2 0 10^2e+5 0 10^f+1 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+3 0 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2d+2 0 10^2e+5 0 10^f+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+3 0 10^2d+7 0 10^2e+1 0 10^f+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2d+2 0 10^2e+5 0 10^f+1 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+1 1100 10^2c+4 0 10^2d+2 0 10^2e+5 0 10^f+1 0^inf
                        chain_step(0, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 010 0001^b 010 <B 0 10^2c+5 0 10^2d+2 0 10^2e+5 0 10^f+1 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2c+4 0 10^2d+2 0 10^2e+5 0 10^f+1 0^inf
                        chain_step(0, "b+c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b+c+1 010 B> 10^2d+3 0 10^2e+5 0 10^f+1 0^inf
                        rule_step(4, &[("a", "d")]),
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        rule_step(7, &[("a", "d+2")]),
                        // 0^inf 1100101 0001^a 011100101 0001^b+c 010 <B 0100 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(1, "b+c"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+2c+4 0 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "b+c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 B> 10^2d+8 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "d+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 0001^d+3 010 B> 10^2e+2 0 10^f+1 0^inf
                        chain_step(0, "e+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 0001^d+3 010 0001^e 010 B> 10^f+2 0^inf
                        rule_step(3, &[("a", "f")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 0001^d+3 010 0001^e 01010 <B 0100 10^f+1 0^inf
                        chain_step(2, "e"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 0001^d+3 01010 <B 0100 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "d+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 01010 <B 0100 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "b+c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+2c+3 0 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+3 0 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                    ]),
                },
                // 32: 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^2 0 10^2c+1 0 10^d+1 0^inf  -->  0^inf 1100101 B> 10^2a+8 0 10^2b+2c+7 0 10^d 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^2 0 10^2c+1 0 10^d+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+8 0 10^2b+2c+7 0 10^d 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^2 0 10^2c+1 0 10^d+1 0^inf
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 0 10^2 0 10^2c+1 0 10^d+1 0^inf
                        rule_step(4, &[("a", "b")]),
                        rule_step(5, &[("a", "b")]),
                        // 0^inf 1100101 0001^a+1 1100101 B> 10^2b+3 00 10^2c+1 0 10^d+1 0^inf
                        chain_step(0, "b+1"),
                        base_step(6),
                        // 0^inf 1100101 0001^a+1 1100101 0001^b+1 0101 B> 10^2c+1 0 10^d+1 0^inf
                        chain_step(0, "c"),
                        base_step(6),
                        // 0^inf 1100101 0001^a+1 1100101 0001^b+1 0101 0001^c 010 <B 00 10^d 0^inf
                        chain_step(1, "c"),
                        base_step(4),
                        // 0^inf 1100101 0001^a+1 1100101 0001^b+1 010 <B 01100 10^2c 0 10^d 0^inf
                        chain_step(1, "b+1"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+5 1100 10^2c 0 10^d 0^inf
                        chain_step(0, "b+2"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 010 <B 0 10^2c+1 0 10^d 0^inf
                        chain_step(1, "b+2"),
                        base_step(107),
                        // 0^inf 1100101 0001^a 010 <B 0100 10^2b+2c+8 0 10^d 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+5 0 10^2b+2c+8 0 10^d 0^inf
                        chain_step(0, "a+2"),
                        base_step(6),
                        // 0^inf 1100101 0001^a+2 010 <B 00 10^2b+2c+7 0 10^d 0^inf
                        chain_step(1, "a+2"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+8 0 10^2b+2c+7 0 10^d 0^inf
                    ]),
                },
                // 33: 0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^c+1 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+1 0 10^c+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^c+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+1 0 10^c+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^c+1 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+2 0 10^2c+1 0^inf
                        chain_step(0, "b+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 010 B> 10^c+2 0^inf
                        rule_step(3, &[("a", "c")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 01010 <B 0100 10^c+1 0^inf
                        chain_step(2, "b"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 01010 <B 0100 10^2b+1 0 10^c+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+1 0 10^c+1 0^inf
                    ]),
                },
                // 34: 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 0 10^c+2 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+4 1100 10^c+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 0 10^c+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+4 1100 10^c+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 0 10^c+2 0^inf
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 0 10^3 0 10^c+2 0^inf
                        rule_step(4, &[("a", "b")]),
                        rule_step(5, &[("a", "b")]),
                        rule_step(6, &[("a", "b+1")]),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+5 0^2 10^c+2 0^inf
                        chain_step(0, "b+2"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 0101 B> 10^c+2 0^inf
                        rule_step(3, &[("a", "c")]),
                        base_step(4),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 01010 <B 01100 10^c+1 0^inf
                        chain_step(2, "b+2"),
                        base_step(165),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^4 0 10^2b+4 1100 10^c+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+4 1100 10^c+1 0^inf
                    ]),
                },
                // 35: 0^inf 1100101 B> 10^2a+2 0 10^2b+4 01 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+4 01 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+4 01 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+5 01 0^inf
                        rule_step(4, &[("a", "b+1")]),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+3 0^inf
                        rule_step(3, &[("a", "2b+1")]),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b+2 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 0^inf
                    ]),
                },
                // 36: 0^inf 1100101 B> 10^2a+2 0 10^2b 001 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a 0 10^2b 11 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b 001 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a 0 10^2b 11 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b 001 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+1 001 0^inf
                        chain_step(0, "b"),
                        base_step(16),
                        // 0^inf 1100101 0001^a 010 0001^b 01010 <B 011 0^inf
                        chain_step(2, "b"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 01010 <B 0100 10^2b 11 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a 0 10^2b 11 0^inf
                    ]),
                },
                // 37: 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^2 11 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+5 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^2 11 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+5 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^2 11 0^inf
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 0 10^2 11 0^inf
                        rule_step(4, &[("a", "b")]),
                        rule_step(5, &[("a", "b")]),
                        rule_step(6, &[("a", "b+1")]),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+6 0^inf
                        rule_step(3, &[("a", "2b+4")]),
                        base_step(165),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^4 0 10^2b+5 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+5 0^inf
                    ]),
                },
                // 38: 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+4 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+4 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 0^inf
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 0 10^3 0^inf
                        rule_step(4, &[("a", "b")]),
                        rule_step(5, &[("a", "b")]),
                        rule_step(6, &[("a", "b+1")]),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+5 0^inf
                        rule_step(3, &[("a", "2b+3")]),
                        base_step(165),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^4 0 10^2b+4 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+4 0^inf
                    ]),
                },
                // 39: 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+5 0 10^e+5 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 01100 10^2c+3 0 10^2d+7 0 10^e+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+5 0 10^e+5 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 01100 10^2c+3 0 10^2d+7 0 10^e+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+5 0 10^e+5 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+6 01100 10^2c+1 0 10^2d+5 0 10^e+5 0^inf
                        chain_step(0, "b+3"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b+2 011100101 B> 10^2c+1 0 10^2d+5 0 10^e+5 0^inf
                        rule_step(5, &[("a", "c")]),
                        rule_step(6, &[("a", "c+1")]),
                        rule_step(7, &[("a", "c+2")]),
                        // 0^inf 1100101 0001^a 010 0001^b+1 010 <B 0100 10^2c+7 0 10^2d+2 0 10^e+5 0^inf
                        chain_step(1, "b+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2 0 10^2c+7 0 10^2d+2 0 10^e+5 0^inf
                        chain_step(0, "b+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 B> 10^2c+8 0 10^2d+2 0 10^e+5 0^inf
                        chain_step(0, "c+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 010 B> 10^2d+3 0 10^e+5 0^inf
                        rule_step(4, &[("a", "d")]),
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        rule_step(7, &[("a", "d+2")]),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+2 010 <B 0100 10^2d+7 0 10^e+1 0^inf
                        chain_step(1, "c+2"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 B> 10^2c+4 0 10^2d+7 0 10^e+1 0^inf
                        chain_step(0, "c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 010 B> 10^2d+8 0 10^e+1 0^inf
                        chain_step(0, "d+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 010 0001^d+3 010 B> 10^e+2 0^inf
                        rule_step(3, &[("a", "e")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 010 0001^d+3 01010 <B 0100 10^e+1 0^inf
                        chain_step(2, "d+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 01010 <B 0100 10^2d+7 0 10^e+1 0^inf
                        chain_step(2, "c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 011100101 0001^b 01010 <B 0 10^2 01100 10^2c+3 0 10^2d+7 0 10^e+1 0^inf
                        chain_step(2, "b"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b+2 01100 10^2c+3 0 10^2d+7 0 10^e+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 01100 10^2c+3 0 10^2d+7 0 10^e+1 0^inf
                    ]),
                },
                // 40: 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+4 01100 10^2d+1 0 10^2e+5 0 10^f+5 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+4 01100 10^2c+3 0 10^2d+3 0 10^2e+7 0 10^f+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+4 01100 10^2d+1 0 10^2e+5 0 10^f+5 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+4 01100 10^2c+3 0 10^2d+3 0 10^2e+7 0 10^f+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+4 01100 10^2d+1 0 10^2e+5 0 10^f+5 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+2 01100 10^2c+4 01100 10^2d+1 0 10^2e+5 0 10^f+5 0^inf
                        chain_step(0, "b+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 B> 10^2c+4 01100 10^2d+1 0 10^2e+5 0 10^f+5 0^inf
                        chain_step(0, "c+2"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 0001^c+1 011100101 B> 10^2d+1 0 10^2e+5 0 10^f+5 0^inf
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        rule_step(7, &[("a", "d+2")]),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 0001^c 010 <B 0100 10^2d+7 0 10^2e+2 0 10^f+5 0^inf
                        chain_step(1, "c"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 B> 10^2c+4 0 10^2d+7 0 10^2e+2 0 10^f+5 0^inf
                        chain_step(0, "c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 B> 10^2d+8 0 10^2e+2 0 10^f+5 0^inf
                        chain_step(0, "d+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+3 010 B> 10^2e+3 0 10^f+5 0^inf
                        rule_step(4, &[("a", "e")]),
                        rule_step(5, &[("a", "e")]),
                        rule_step(6, &[("a", "e+1")]),
                        rule_step(7, &[("a", "e+2")]),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+2 010 <B 0100 10^2e+7 0 10^f+1 0^inf
                        chain_step(1, "d+2"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 011100101 B> 10^2d+4 0 10^2e+7 0 10^f+1 0^inf
                        chain_step(0, "d+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 011100101 0001^d+1 010 B> 10^2e+8 0 10^f+1 0^inf
                        chain_step(0, "e+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 011100101 0001^d+1 010 0001^e+3 010 B> 10^f+2 0^inf
                        rule_step(3, &[("a", "f")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 011100101 0001^d+1 010 0001^e+3 01010 <B 0100 10^f+1 0^inf
                        chain_step(2, "e+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 011100101 0001^d+1 01010 <B 0100 10^2e+7 0 10^f+1 0^inf
                        chain_step(2, "d+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 01010 <B 0 10^2 01100 10^2d+3 0 10^2e+7 0 10^f+1 0^inf
                        chain_step(2, "c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 0001^b 010 <B 0 10^2 01100 10^2c+4 01100 10^2d+3 0 10^2e+7 0 10^f+1 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+1 01100 10^2c+4 01100 10^2d+3 0 10^2e+7 0 10^f+1 0^inf
                        rule_step(5, &[("a", "b")]),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+4 0 10^2c+4 01100 10^2d+3 0 10^2e+7 0 10^f+1 0^inf
                        chain_step(0, "b+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 B> 10^2c+5 01100 10^2d+3 0 10^2e+7 0 10^f+1 0^inf
                        rule_step(4, &[("a", "c+1")]),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 B> 10^2c+4 0 10^2d+3 0 10^2e+7 0 10^f+1 0^inf
                        chain_step(0, "c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 B> 10^2d+4 0 10^2e+7 0 10^f+1 0^inf
                        chain_step(0, "d+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+1 010 B> 10^2e+8 0 10^f+1 0^inf
                        chain_step(0, "e+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+1 010 0001^e+3 010 B> 10^f+2 0^inf
                        rule_step(3, &[("a", "f")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+1 010 0001^e+3 01010 <B 0100 10^f+1 0^inf
                        chain_step(2, "e+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+1 01010 <B 0100 10^2e+7 0 10^f+1 0^inf
                        chain_step(2, "d+1"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 01010 <B 0100 10^2d+3 0 10^2e+7 0 10^f+1 0^inf
                        chain_step(2, "c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 01010 <B 0 10^2 01100 10^2c+3 0 10^2d+3 0 10^2e+7 0 10^f+1 0^inf
                        chain_step(2, "b+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+4 01100 10^2c+3 0 10^2d+3 0 10^2e+7 0 10^f+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+4 01100 10^2c+3 0 10^2d+3 0 10^2e+7 0 10^f+1 0^inf
                    ]),
                },
                // 41: 0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2d+5 0 10^2e+4n+1 0 10^f+1 0^inf  -->  0^inf 1100101 B> 10^2a+4n+2 01100 10^2b+4 01100 10^2c+2n+1 0 10^2d+2n+5 0 10^2e+1 0 10^f+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2d+5 0 10^2e+4n+1 0 10^f+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+4n+2 01100 10^2b+4 01100 10^2c+2n+1 0 10^2d+2n+5 0 10^2e+1 0 10^f+1 0^inf").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2d+5 0 10^2e+4n+5 0 10^f+1 0^inf
                            chain_step(0, "a+1"),
                            base_step(49),
                            // 0^inf 1100101 0001^a 011100101 B> 10^2b+4 01100 10^2c+1 0 10^2d+5 0 10^2e+4n+5 0 10^f+1 0^inf
                            chain_step(0, "b+2"),
                            base_step(49),
                            // 0^inf 1100101 0001^a 011100101 0001^b+1 011100101 B> 10^2c+1 0 10^2d+5 0 10^2e+4n+5 0 10^f+1 0^inf
                            rule_step(5, &[("a", "c")]),
                            rule_step(6, &[("a", "c+1")]),
                            rule_step(7, &[("a", "c+2")]),
                            // 0^inf 1100101 0001^a 011100101 0001^b 010 <B 0100 10^2c+7 0 10^2d+2 0 10^2e+4n+5 0 10^f+1 0^inf
                            chain_step(1, "b"),
                            base_step(146),
                            // 0^inf 1100101 0001^a 1100101 B> 10^2b+4 0 10^2c+7 0 10^2d+2 0 10^2e+4n+5 0 10^f+1 0^inf
                            chain_step(0, "b+2"),
                            base_step(5),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 010 B> 10^2c+8 0 10^2d+2 0 10^2e+4n+5 0 10^f+1 0^inf
                            chain_step(0, "c+4"),
                            base_step(5),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+3 010 B> 10^2d+3 0 10^2e+4n+5 0 10^f+1 0^inf
                            rule_step(4, &[("a", "d")]),
                            rule_step(5, &[("a", "d")]),
                            rule_step(6, &[("a", "d+1")]),
                            rule_step(7, &[("a", "d+2")]),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+2 010 <B 0100 10^2d+7 0 10^2e+4n+1 0 10^f+1 0^inf
                            chain_step(1, "c+2"),
                            base_step(22),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 B> 10^2c+4 0 10^2d+7 0 10^2e+4n+1 0 10^f+1 0^inf
                            chain_step(0, "c+2"),
                            base_step(5),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 B> 10^2d+8 0 10^2e+4n+1 0 10^f+1 0^inf
                            chain_step(0, "d+4"),
                            base_step(5),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+3 010 B> 10^2e+4n+2 0 10^f+1 0^inf
                            chain_step(0, "e+2n+1"),
                            base_step(5),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+3 010 0001^e+2n 010 B> 10^f+2 0^inf
                            rule_step(3, &[("a", "f")]),
                            base_step(9),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+3 010 0001^e+2n 01010 <B 0 00 10^f+1 0^inf
                            chain_step(2, "e+2n"),
                            base_step(9),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+3 01010 <B 0100 10^2e+4n+1 0 10^f+1 0^inf
                            chain_step(2, "d+3"),
                            base_step(9),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 01010 <B 0100 10^2d+7 0 10^2e+4n+1 0 10^f+1 0^inf
                            chain_step(2, "c+1"),
                            base_step(39),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 01010 <B 0 10^2 01100 10^2c+3 0 10^2d+7 0 10^2e+4n+1 0 10^f+1 0^inf
                            chain_step(2, "b+1"),
                            base_step(39),
                            // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+4 01100 10^2c+3 0 10^2d+7 0 10^2e+4n+1 0 10^f+1 0^inf
                            chain_step(1, "a"),
                            base_step(186),
                            // 0^inf 1100101 B> 10^2a+6 01100 10^2b+4 01100 10^2c+3 0 10^2d+7 0 10^2e+4n+1 0 10^f+1 0^inf
                            induction_step(&[("a", "a+2"), ("b", "b"), ("c", "c+1"), ("d", "d+1"), ("e", "e"), ("f", "f")]),
                            // 0^inf 1100101 B> 10^2a+4n+6 01100 10^2b+4 01100 10^2c+2n+3 0 10^2d+2n+7 0 10^2e+1 0 10^f+1 0^inf
                        ],
                    },
                },
                // 42: 0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2d+5 0 10^3 0 10^e+2 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+8 0 10^2d+4 1100 10^e+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2d+5 0 10^3 0 10^e+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+8 0 10^2d+4 1100 10^e+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2d+5 0 10^3 0 10^e+2 0^inf
                        chain_step(0, "a+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+4 01100 10^2c+1 0 10^2d+5 0 10^3 0 10^e+2 0^inf
                        chain_step(0, "b+2"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 011100101 0001^b+1 011100101 B> 10^2c+1 0 10^2d+5 0 10^3 0 10^e+2 0^inf
                        rule_step(5, &[("a", "c")]),
                        rule_step(6, &[("a", "c+1")]),
                        rule_step(7, &[("a", "c+2")]),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 <B 0100 10^2c+7 0 10^2d+2 0 10^3 0 10^e+2 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+4 0 10^2c+7 0 10^2d+2 0 10^3 0 10^e+2 0^inf
                        chain_step(0, "b+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 B> 10^2c+8 0 10^2d+2 0 10^3 0 10^e+2 0^inf
                        chain_step(0, "c+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+3 010 B> 10^2d+3 0 10^3 0 10^e+2 0^inf
                        rule_step(4, &[("a", "d")]),
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+2 001100101 B> 10^2d+5 00 10^e+2 0^inf
                        chain_step(0, "d+2"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+2 001100101 0001^d+2 0101 B> 10^e+2 0^inf
                        rule_step(3, &[("a", "e")]),
                        base_step(4),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+2 001100101 0001^d+2 01010 <B 01100 10^e+1 0^inf
                        chain_step(2, "d+2"),
                        base_step(165),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+2 01010 <B 0 10^4 0 10^2d+4 1100 10^e+1 0^inf
                        chain_step(2, "c+2"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 01010 <B 0100 10^2c+8 0 10^2d+4 1100 10^e+1 0^inf
                        chain_step(2, "b+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+3 0 10^2c+8 0 10^2d+4 1100 10^e+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+8 0 10^2d+4 1100 10^e+1 0^inf
                    ]),
                },
                // 43: 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 0 10^2c+2 1100 10^2 0^inf  -->  0^inf 1100101 B> 10^2a+8 0 10^2b+6 1100 10^2c+1 0 10^4 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 0 10^2c+2 1100 10^2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+8 0 10^2b+6 1100 10^2c+1 0 10^4 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 0 10^2c+2 1100 10^2 0^inf
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 0 10^3 0 10^2c+2 1100 10^2 0^inf
                        rule_step(4, &[("a", "b")]),
                        rule_step(5, &[("a", "b")]),
                        rule_step(6, &[("a", "b+1")]),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+5 00 10^2c+2 1100 10^2 0^inf
                        chain_step(0, "b+2"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 0101 B> 10^2c+2 1100 10^2 0^inf
                        chain_step(0, "c+1"),
                        base_step(198),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 0101 0001^c 010 <B 0100 10^4 0^inf
                        chain_step(1, "c"),
                        base_step(4),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 010 <B 01100 10^2c+1 0 10^4 0^inf
                        chain_step(1, "b+2"),
                        base_step(107),
                        // 0^inf 1100101 0001^a 010 <B 0100 10^2b+7 1100 10^2c+1 0 10^4 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+5 0 10^2b+7 1100 10^2c+1 0 10^4 0^inf
                        chain_step(0, "a+2"),
                        base_step(6),
                        // 0^inf 1100101 0001^a+2 010 <B 00 10^2b+6 1100 10^2c+1 0 10^4 0^inf
                        chain_step(1, "a+2"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+8 0 10^2b+6 1100 10^2c+1 0 10^4 0^inf
                    ]),
                },
                // 44: 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 0 10^2c+2 1100 10^d+3 0^inf  -->  0^inf 1100101 B> 10^2a+8 0 10^2b+6 1100 10^2c+1 0 10^4 0 10^d+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 0 10^2c+2 1100 10^d+3 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+8 0 10^2b+6 1100 10^2c+1 0 10^4 0 10^d+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 0 10^2c+2 1100 10^d+3 0^inf
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 0 10^3 0 10^2c+2 1100 10^d+3 0^inf
                        rule_step(4, &[("a", "b")]),
                        rule_step(5, &[("a", "b")]),
                        rule_step(6, &[("a", "b+1")]),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+5 00 10^2c+2 1100 10^d+3 0^inf
                        chain_step(0, "b+2"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 0101 B> 10^2c+2 1100 10^d+3 0^inf
                        chain_step(0, "c+1"),
                        base_step(18),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 0101 0001^c+1 100101 B> 10^d+2 0^inf
                        rule_step(3, &[("a", "d")]),
                        base_step(174),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 0101 0001^c 010 <B 0100 10^4 0 10^d+1 0^inf
                        chain_step(1, "c"),
                        base_step(4),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 010 <B 01100 10^2c+1 0 10^4 0 10^d+1 0^inf
                        chain_step(1, "b+2"),
                        base_step(107),
                        // 0^inf 1100101 0001^a 010 <B 0100 10^2b+7 1100 10^2c+1 0 10^4 0 10^d+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+5 0 10^2b+7 1100 10^2c+1 0 10^4 0 10^d+1 0^inf
                        chain_step(0, "a+2"),
                        base_step(6),
                        // 0^inf 1100101 0001^a+2 010 <B 00 10^2b+6 1100 10^2c+1 0 10^4 0 10^d+1 0^inf
                        chain_step(1, "a+2"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+8 0 10^2b+6 1100 10^2c+1 0 10^4 0 10^d+1 0^inf
                    ]),
                },
                // 45: 0^inf 1100101 B> 10^2a+2 0 10^2b+2 0100 10^c+2 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b 1100 10^c+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+2 0100 10^c+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b 1100 10^c+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+2 0100 10^c+2 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+3 0100 10^c+2 0^inf
                        rule_step(4, &[("a", "b")]),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+1 00 10^c+2 0^inf
                        chain_step(0, "b"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 011100101 0001^b 0101 B> 10^c+2 0^inf
                        rule_step(3, &[("a", "c")]),
                        base_step(4),
                        // 0^inf 1100101 0001^a 011100101 0001^b 01010 <B 01100 10^c+1 0^inf
                        chain_step(2, "b"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b 1100 10^c+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b 1100 10^c+1 0^inf
                    ]),
                },
                // 46: 0^inf 1100101 B> 10^2a+2 0 10^2b+3 01100 10^2c+2 1100 10^d+7 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+4 0 10^2c+3 0 10^9 0 10^d+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+3 01100 10^2c+2 1100 10^d+7 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+4 0 10^2c+3 0 10^9 0 10^d+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+3 01100 10^2c+2 1100 10^d+7 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+4 01100 10^2c+2 1100 10^d+7 0^inf
                        chain_step(0, "b+2"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b+1 011100101 B> 10^2c+2 1100 10^d+7 0^inf
                        chain_step(0, "c+1"),
                        base_step(18),
                        // 0^inf 1100101 0001^a 010 0001^b+1 011100101 0001^c+1 100101 B> 10^d+6 0^inf
                        rule_step(3, &[("a", "d+4")]),
                        base_step(174),
                        // 0^inf 1100101 0001^a 010 0001^b+1 011100101 0001^c 010 <B 0100 10^4 0 10^d+5 0^inf
                        chain_step(1, "c"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 010 0001^b+1 1100101 B> 10^2c+4 0 10^4 0 10^d+5 0^inf
                        chain_step(0, "c+2"),
                        base_step(1042),
                        // 0^inf 1100101 0001^a 010 0001^b+1 1100101 0001^c 010 <B 0100 10^9 0 10^d+1 0^inf
                        chain_step(1, "c"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 010 0001^b 001100101 B> 10^2c+4 0 10^9 0 10^d+1 0^inf
                        chain_step(0, "c+2"),
                        base_step(50),
                        // 0^inf 1100101 0001^a 010 0001^b 001100101 0001^c+1 010 0001^4 010 B> 10^d+2 0^inf
                        rule_step(3, &[("a", "d")]),
                        base_step(306),
                        // 0^inf 1100101 0001^a 010 0001^b 001100101 0001^c+1 01010 <B 0100 10^9 0 10^d+1 0^inf
                        chain_step(2, "c+1"),
                        base_step(165),
                        // 0^inf 1100101 0001^a 010 0001^b 01010 <B 0 10^4 0 10^2c+3 0 10^9 0 10^d+1 0^inf
                        chain_step(2, "b"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 01010 <B 0100 10^2b+4 0 10^2c+3 0 10^9 0 10^d+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+4 0 10^2c+3 0 10^9 0 10^d+1 0^inf
                    ]),
                },
                // 47: 0^inf 1100101 B> 10^2a+4 0 10^2b+2 00 10^2c+1 0 10^2d+3 0 10^e+5 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+2c+3 0 10^2d+7 0 10^e+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b+2 00 10^2c+1 0 10^2d+3 0 10^e+5 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+2c+3 0 10^2d+7 0 10^e+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b+2 00 10^2c+1 0 10^2d+3 0 10^e+5 0^inf
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 00 10^2c+1 0 10^2d+3 0 10^e+5 0^inf
                        chain_step(0, "b+1"),
                        base_step(6),
                        // 0^inf 1100101 0001^a+1 010 0001^b+1 0101 B> 10^2c+1 0 10^2d+3 0 10^e+5 0^inf
                        chain_step(0, "c"),
                        base_step(6),
                        // 0^inf 1100101 0001^a+1 010 0001^b+1 0101 0001^c 010 <B 00 10^2d+2 0 10^e+5 0^inf
                        chain_step(1, "c"),
                        base_step(4),
                        // 0^inf 1100101 0001^a+1 010 0001^b+1 010 <B 01100 10^2c 0 10^2d+2 0 10^e+5 0^inf
                        chain_step(1, "b+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a+1 011100101 B> 10^2b+1 1100 10^2c 0 10^2d+2 0 10^e+5 0^inf
                        chain_step(0, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 010 <B 0 10^2c+1 0 10^2d+2 0 10^e+5 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a+1 1100101 B> 10^2b+2c+4 0 10^2d+2 0 10^e+5 0^inf
                        chain_step(0, "b+c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 1100101 0001^b+c+1 010 B> 10^2d+3 0 10^e+5 0^inf
                        rule_step(4, &[("a", "d")]),
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        rule_step(7, &[("a", "d+2")]),
                        // 0^inf 1100101 0001^a+1 1100101 0001^b+c 010 <B 0100 10^2d+7 0 10^e+1 0^inf
                        chain_step(1, "b+c"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+2c+4 0 10^2d+7 0 10^e+1 0^inf
                        chain_step(0, "b+c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 001100101 0001^b+c+1 010 B> 10^2d+8 0 10^e+1 0^inf
                        chain_step(0, "d+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 001100101 0001^b+c+1 010 0001^d+3 010 B> 10^e+2 0^inf
                        rule_step(3, &[("a", "e")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 001100101 0001^b+c+1 010 0001^d+3 01010 <B 0100 10^e+1 0^inf
                        chain_step(2, "d+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 001100101 0001^b+c+1 01010 <B 0100 10^2d+7 0 10^e+1 0^inf
                        chain_step(2, "b+c+1"),
                        base_step(165),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^4 0 10^2b+2c+3 0 10^2d+7 0 10^e+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+2c+3 0 10^2d+7 0 10^e+1 0^inf
                    ]),
                },
                // 48: 0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^e+1 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^e+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^e+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^e+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^e+1 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+2 0 10^2c+1 0 10^2d+1 0 10^e+1 0^inf
                        chain_step(0, "b+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 010 B> 10^2c+2 0 10^2d+1 0 10^e+1 0^inf
                        chain_step(0, "c+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 B> 10^2d+2 0 10^e+1 0^inf
                        chain_step(0, "d+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 0001^d 010 B> 10^e+2 0^inf
                        rule_step(3, &[("a", "e")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 010 0001^d 01010 <B 0100 10^e+1 0^inf
                        chain_step(2, "d"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 010 0001^c 01010 <B 0100 10^2d+1 0 10^e+1 0^inf
                        chain_step(2, "c"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 01010 <B 0100 10^2c+1 0 10^2d+1 0 10^e+1 0^inf
                        chain_step(2, "b"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 01010 <B 0100 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^e+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+1 0 10^2c+1 0 10^2d+1 0 10^e+1 0^inf
                    ]),
                },
                // 49: 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2d+2 0 10^e+5 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+3 0 10^2d+7 0 10^e+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2d+2 0 10^e+5 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+3 0 10^2d+7 0 10^e+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2d+2 0 10^e+5 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+1 1100 10^2c+4 0 10^2d+2 0 10^e+5 0^inf
                        chain_step(0, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 010 0001^b 010 <B 0 10^2c+5 0 10^2d+2 0 10^e+5 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2c+4 0 10^2d+2 0 10^e+5 0^inf
                        chain_step(0, "b+c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b+c+1 010 B> 10^2d+3 0 10^e+5 0^inf
                        rule_step(4, &[("a", "d")]),
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        rule_step(7, &[("a", "d+2")]),
                        // 0^inf 1100101 0001^a 011100101 0001^b+c 010 <B 0100 10^2d+7 0 10^e+1 0^inf
                        chain_step(1, "b+c"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+2c+4 0 10^2d+7 0 10^e+1 0^inf
                        chain_step(0, "b+c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 B> 10^2d+8 0 10^e+1 0^inf
                        chain_step(0, "d+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 0001^d+3 010 B> 10^e+2 0^inf
                        rule_step(3, &[("a", "e")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 0001^d+3 01010 <B 0100 10^e+1 0^inf
                        chain_step(2, "d+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 01010 <B 0100 10^2d+7 0 10^e+1 0^inf
                        chain_step(2, "b+c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+2c+3 0 10^2d+7 0 10^e+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^4a+6 01100 10^2b+2c+3 0 10^2d+7 0 10^e+1 0^inf
                    ]),
                },
                // 50: 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0100 10^2c+2 1100 10^d+3 0^inf  -->  0^inf 1100101 B> 10^2a+8 0 10^2b+2c+8 0 10^3 0 10^d+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b+2 0100 10^2c+2 1100 10^d+3 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+8 0 10^2b+2c+8 0 10^3 0 10^d+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0100 10^2c+2 1100 10^d+3 0^inf
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 0100 10^2c+2 1100 10^d+3 0^inf
                        rule_step(4, &[("a", "b")]),
                        // 0^inf 1100101 0001^a+1 011100101 B> 10^2b+1 00 10^2c+2 1100 10^d+3 0^inf
                        chain_step(0, "b"),
                        base_step(6),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 0101 B> 10^2c+2 1100 10^d+3 0^inf
                        chain_step(0, "c+1"),
                        base_step(18),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 0101 0001^c+1 100101 B> 10^d+2 0^inf
                        rule_step(3, &[("a", "d")]),
                        base_step(174),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 0101 0001^c 010 <B 0100 10^4 0 10^d+1 0^inf
                        chain_step(1, "c"),
                        base_step(4),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 010 <B 01100 10^2c+1 0 10^4 0 10^d+1 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a+1 1100101 B> 10^2b+3 1100 10^2c+1 0 10^4 0 10^d+1 0^inf
                        chain_step(0, "b+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a+1 1100101 0001^b+1 010 <B 0 10^2c+2 0 10^4 0 10^d+1 0^inf
                        chain_step(1, "b+1"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+2c+7 0 10^4 0 10^d+1 0^inf
                        rule_step(7, &[("a", "b+c+3")]),
                        // 0^inf 1100101 0001^a 010 <B 0100 10^2b+2c+9 0 10^3 0 10^d+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+5 0 10^2b+2c+9 0 10^3 0 10^d+1 0^inf
                        chain_step(0, "a+2"),
                        base_step(6),
                        // 0^inf 1100101 0001^a+2 010 <B 00 10^2b+2c+8 0 10^3 0 10^d+1 0^inf
                        chain_step(1, "a+2"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+8 0 10^2b+2c+8 0 10^3 0 10^d+1 0^inf
                    ]),
                },
                // 51: 0^inf 1100101 B> 10^2a+2 0 10^2b+2 0 10^2 01 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+2 11 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+2 0 10^2 01 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+2 11 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+2 0 10^2 01 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+3 0 10^2 01 0^inf
                        rule_step(4, &[("a", "b")]),
                        rule_step(5, &[("a", "b")]),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+3 001 0^inf
                        chain_step(0, "b+1"),
                        base_step(16),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 01010 <B 011 0^inf
                        chain_step(2, "b+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+2 11 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+2 11 0^inf
                    ]),
                },
                // 52: 0^inf 1100101 B> 10^2a+2 01100 10^2b 11 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 01100 10^2b 11 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 01100 10^2b 11 0^inf
                        chain_step(0, "a+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b 11 0^inf
                        chain_step(0, "b"),
                        base_step(16),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 <B 01 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+4 0^inf
                        rule_step(3, &[("a", "2b+2")]),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+3 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0^inf
                    ]),
                },
                // 53: 0^inf 1100101 B> 10^2a+2 0 10^2b+2 0 10^2 0 10^c+2 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+2 1100 10^c+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+2 0 10^2 0 10^c+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+2 1100 10^c+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+2 0 10^2 0 10^c+2 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 0 10^2 0 10^c+2 0^inf
                        rule_step(4, &[("a", "b")]),
                        rule_step(5, &[("a", "b")]),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+3 0^2 10^c+2 0^inf
                        chain_step(0, "b+1"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 0101 B> 10^c+2 0^inf
                        rule_step(3, &[("a", "c")]),
                        base_step(4),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 01010 <B 01100 10^c+1 0^inf
                        chain_step(2, "b+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+2 1100 10^c+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+2 1100 10^c+1 0^inf
                    ]),
                },
                // 54: 0^inf 1100101 B> 10^2a+2 01100 10^2b+2 11001 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+4 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 01100 10^2b+2 11001 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+4 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 01100 10^2b+2 11001 0^inf
                        chain_step(0, "a+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2 11001 0^inf
                        chain_step(0, "b+1"),
                        base_step(246),
                        // 0^inf 1100101 0001^a 011100101 0001^b 01010 <B 0 10^4 0^inf
                        chain_step(2, "b"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b+4 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+4 0^inf
                    ]),
                },
                // 55: 0^inf 1100101 B> 10^2a+2 01100 10^2b+2 1100 10^2 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^4 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 01100 10^2b+2 1100 10^2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^4 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 01100 10^2b+2 1100 10^2 0^inf
                        chain_step(0, "a+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2 1100 10^2 0^inf
                        chain_step(0, "b+1"),
                        base_step(198),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 <B 0100 10^4 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+4 0 10^4 0^inf
                        chain_step(0, "b+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 B> 10^5 0^inf
                        rule_step(3, &[("a", "3")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 01010 <B 0100 10^4 0^inf
                        chain_step(2, "b+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+3 0 10^4 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^4 0^inf
                    ]),
                },
                // 56: 0^inf 1100101 B> 10^2a+2 01100 10^2b+2 1100 10^3 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+4 01100 10^2 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 01100 10^2b+2 1100 10^3 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+4 01100 10^2 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 01100 10^2b+2 1100 10^3 0^inf
                        chain_step(0, "a+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2 1100 10^3 0^inf
                        chain_step(0, "b+1"),
                        base_step(220),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 <B 0100 10^4 01 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+4 0 10^4 01 0^inf
                        chain_step(0, "b+2"),
                        base_step(306),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 01010 <B 0 10^2 01100 10^2 0^inf
                        chain_step(2, "b+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+4 01100 10^2 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+4 01100 10^2 0^inf
                    ]),
                },
                // 57: 0^inf 1100101 B> 10^2a+2 01100 10^2b+2 01100 10^c+2 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 01100 10^c+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 01100 10^2b+2 01100 10^c+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 01100 10^c+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 01100 10^2b+2 01100 10^c+2 0^inf
                        chain_step(0, "a+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2 01100 10^c+2 0^inf
                        chain_step(0, "b+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 B> 10^c+2 0^inf
                        rule_step(3, &[("a", "c")]),
                        base_step(39),
                        // 0^inf 1100101 0001^a 011100101 0001^b 01010 <B 0 10^2 01100 10^c+1 0^inf
                        chain_step(2, "b"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b+2 01100 10^c+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 01100 10^c+1 0^inf
                    ]),
                },
                // 58: 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+2 011001 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+2 01100 10^2c+2 011 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+2 011001 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+2 01100 10^2c+2 011 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+2 011001 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+2 01100 10^2c+2 011001 0^inf
                        chain_step(0, "b+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 B> 10^2c+2 011001 0^inf
                        chain_step(0, "c+1"),
                        base_step(94),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 0001^c 01010 <B 0 10^2 011 0^inf
                        chain_step(2, "c"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 0001^b 01010 <B 0 10^2 01100 10^2c+2 011 0^inf
                        chain_step(2, "b"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 01010 <B 0100 10^2b+2 01100 10^2c+2 011 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+2 01100 10^2c+2 011 0^inf
                    ]),
                },
                // 59: 0^inf 1100101 B> 10^2a+2 0 10^2b+2 001100 10^2c+2 011 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+7 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+2 001100 10^2c+2 011 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+7 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+2 001100 10^2c+2 011 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+3 001100 10^2c+2 011 0^inf
                        chain_step(0, "b+1"),
                        base_step(24),
                        // 0^inf 1100101 0001^a 010 0001^b+1 0101100101 B> 10^2c+1 011 0^inf
                        chain_step(0, "c"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 010 0001^b+1 0101100101 0001^c 010 <B 01 0^inf
                        chain_step(1, "c"),
                        base_step(102),
                        // 0^inf 1100101 0001^a 010 0001^b+1 010 <B 01100 10^2c+4 0^inf
                        chain_step(1, "b+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+1 1100 10^2c+4 0^inf
                        chain_step(0, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 <B 0 10^2c+5 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+2c+8 0^inf
                        rule_step(3, &[("a", "2b+2c+6")]),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+2c+7 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+7 0^inf
                    ]),
                },
                // 60: 0^inf 1100101 B> 10^2a+4 01100 10^2b+2 1100 10^4 0^inf  -->  0^inf 1100101 B> 10^2a+8 0 10^2b+9 0 10^4 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 01100 10^2b+2 1100 10^4 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+8 0 10^2b+9 0 10^4 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 01100 10^2b+2 1100 10^4 0^inf
                        chain_step(0, "a+2"),
                        base_step(49),
                        // 0^inf 1100101 0001^a+1 011100101 B> 10^2b+2 1100 10^4 0^inf
                        chain_step(0, "b+1"),
                        base_step(18),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b+1 100101 B> 10^3 0^inf
                        rule_step(3, &[("a", "1")]),
                        base_step(174),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 010 <B 0100 10^4 0 10^2 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a+1 1100101 B> 10^2b+4 0 10^4 0 10^2 0^inf
                        chain_step(0, "b+2"),
                        base_step(612),
                        // 0^inf 1100101 0001^a+1 1100101 0001^b+1 010 <B 0 10^2 01100 10^4 0^inf
                        chain_step(1, "b+1"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+7 01100 10^4 0^inf
                        rule_step(7, &[("a", "b+3")]),
                        // 0^inf 1100101 0001^a 010 <B 0100 10^2b+10 0 10^4 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+5 0 10^2b+10 0 10^4 0^inf
                        chain_step(0, "a+2"),
                        base_step(6),
                        // 0^inf 1100101 0001^a+2 010 <B 00 10^2b+9 0 10^4 0^inf
                        chain_step(1, "a+2"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+8 0 10^2b+9 0 10^4 0^inf
                    ]),
                },
                // 61: 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+2 1100 10^3 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+4 01100 10^2c+3 0 10^2 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+2 1100 10^3 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+4 01100 10^2c+3 0 10^2 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+2 1100 10^3 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+2 01100 10^2c+2 1100 10^3 0^inf
                        chain_step(0, "b+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 B> 10^2c+2 1100 10^3 0^inf
                        chain_step(0, "c+1"),
                        base_step(220),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 0001^c 010 <B 0100 10^4 01 0^inf
                        chain_step(1, "c"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 B> 10^2c+4 0 10^4 01 0^inf
                        chain_step(0, "c+2"),
                        base_step(306),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 01010 <B 0 10^2 01100 10^2 0^inf
                        chain_step(2, "c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 0001^b 010 <B 0 10^2 01100 10^2c+4 01100 10^2 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+1 01100 10^2c+4 01100 10^2 0^inf
                        rule_step(5, &[("a", "b")]),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+4 0 10^2c+4 01100 10^2 0^inf
                        chain_step(0, "b+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 B> 10^2c+5 01100 10^2 0^inf
                        rule_step(4, &[("a", "c+1")]),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 B> 10^2c+4 0 10^2 0^inf
                        chain_step(0, "c+2"),
                        base_step(100),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 01010 <B 0100 10^2 0^inf
                        chain_step(2, "c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 01010 <B 0 10^2 01100 10^2c+3 0 10^2 0^inf
                        chain_step(2, "b+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+4 01100 10^2c+3 0 10^2 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+4 01100 10^2c+3 0 10^2 0^inf
                    ]),
                },
                // 62: 0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+4 0 10^2c+4 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+4 0 10^2c+4 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2 0^inf
                        chain_step(0, "a+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+4 01100 10^2c+1 0 10^2 0^inf
                        chain_step(0, "b+2"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 011100101 0001^b+1 011100101 B> 10^2c+1 0 10^2 0^inf
                        rule_step(5, &[("a", "c")]),
                        rule_step(6, &[("a", "c+1")]),
                        // 0^inf 1100101 0001^a 011100101 0001^b 001100101 B> 10^2c+5 0^inf
                        rule_step(3, &[("a", "2c+3")]),
                        base_step(165),
                        // 0^inf 1100101 0001^a 011100101 0001^b 01010 <B 0 10^4 0 10^2c+4 0^inf
                        chain_step(2, "b"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b+4 0 10^2c+4 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+4 0 10^2c+4 0^inf
                    ]),
                },
                // 63: 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+2 0 10^d+1 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+2 01100 10^2c+1 0 10^d+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+2 0 10^d+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+2 01100 10^2c+1 0 10^d+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+2 0 10^d+1 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+2 01100 10^2c+2 0 10^d+1 0^inf
                        chain_step(0, "b+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 B> 10^2c+2 0 10^d+1 0^inf
                        chain_step(0, "c+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 0001^c 010 B> 10^d+2 0^inf
                        rule_step(3, &[("a", "d")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 0001^c 01010 <B 0100 10^d+1 0^inf
                        chain_step(2, "c"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 0001^b 01010 <B 0 10^2 01100 10^2c+1 0 10^d+1 0^inf
                        chain_step(2, "b"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 01010 <B 0100 10^2b+2 01100 10^2c+1 0 10^d+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+2 01100 10^2c+1 0 10^d+1 0^inf
                    ]),
                },
                // 64: 0^inf 1100101 B> 10^2a+2 0 10^2b 001100 10^2c+3 0 10^d+1 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^3 0 10^2c+1 0 10^d+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b 001100 10^2c+3 0 10^d+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^3 0 10^2c+1 0 10^d+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b 001100 10^2c+3 0 10^d+1 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+1 001100 10^2c+3 0 10^d+1 0^inf
                        chain_step(0, "b"),
                        base_step(24),
                        // 0^inf 1100101 0001^a 010 0001^b 0101100101 B> 10^2c+2 0 10^d+1 0^inf
                        chain_step(0, "c+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 0101100101 0001^c 010 B> 10^d+2 0^inf
                        rule_step(3, &[("a", "d")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 0101100101 0001^c 01010 <B 0100 10^d+1 0^inf
                        chain_step(2, "c"),
                        base_step(234),
                        // 0^inf 1100101 0001^a 010 0001^b 11001010001010 B> 10^2c+2 0 10^d+1 0^inf
                        chain_step(0, "c+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 11001010001010 0001^c 010 B> 10^d+2 0^inf
                        rule_step(3, &[("a", "d")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 11001010001010 0001^c 01010 <B 0100 10^d+1 0^inf
                        chain_step(2, "c"),
                        base_step(120),
                        // 0^inf 1100101 0001^a 010 0001^b 010 <B 0 10^2 01100 10^3 0 10^2c+1 0 10^d+1 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+1 01100 10^3 0 10^2c+1 0 10^d+1 0^inf
                        rule_step(5, &[("a", "b")]),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+4 0 10^3 0 10^2c+1 0 10^d+1 0^inf
                        chain_step(0, "b+2"),
                        base_step(26),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 0100001010 B> 10^2c+2 0 10^d+1 0^inf
                        chain_step(0, "c+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 0100001010 0001^c 010 B> 10^d+2 0^inf
                        rule_step(3, &[("a", "d")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 0100001010 0001^c 01010 <B 0100 10^d+1 0^inf
                        chain_step(2, "c"),
                        base_step(90),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 01010 <B 0100 10^3 0 10^2c+1 0 10^d+1 0^inf
                        chain_step(2, "b+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+3 0 10^3 0 10^2c+1 0 10^d+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^3 0 10^2c+1 0 10^d+1 0^inf
                    ]),
                },
                // 65: 0^inf 1100101 B> 10^2a+2 0 10^2b+2 00 10^2c+1 0 10^d+2 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+3 0 10^d+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+2 00 10^2c+1 0 10^d+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+3 0 10^d+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+2 00 10^2c+1 0 10^d+2 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+3 00 10^2c+1 0 10^d+2 0^inf
                        chain_step(0, "b+1"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 010 0001^b+1 0101 B> 10^2c+1 0 10^d+2 0^inf
                        chain_step(0, "c"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 010 0001^b+1 0101 0001^c 010 <B 00 10^d+1 0^inf
                        chain_step(1, "c"),
                        base_step(4),
                        // 0^inf 1100101 0001^a 010 0001^b+1 010 <B 01100 10^2c 0 10^d+1 0^inf
                        chain_step(1, "b+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+1 1100 10^2c 0 10^d+1 0^inf
                        chain_step(0, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 <B 0 10^2c+1 0 10^d+1 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+2c+4 0 10^d+1 0^inf
                        chain_step(0, "b+c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 B> 10^d+2 0^inf
                        rule_step(3, &[("a", "d")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 01010 <B 0100 10^d+1 0^inf
                        chain_step(2, "b+c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+2c+3 0 10^d+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+3 0 10^d+1 0^inf
                    ]),
                },
                // 66: 0^inf 1100101 B> 10^2a+2 01100 10^2b+2 1100 10^5 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+4 0 10^6 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 01100 10^2b+2 1100 10^5 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+4 0 10^6 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 01100 10^2b+2 1100 10^5 0^inf
                        chain_step(0, "a+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2 1100 10^5 0^inf
                        chain_step(0, "b+1"),
                        base_step(300),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 <B 0100 10^4 0 10^3 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+4 0 10^4 0 10^3 0^inf
                        chain_step(0, "b+2"),
                        base_step(1118),
                        // 0^inf 1100101 0001^a 1100101 0001^b 01010 <B 0 10^4 0 10^6 0^inf
                        chain_step(2, "b"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+4 0 10^6 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+4 0 10^6 0^inf
                    ]),
                },
                // 67: 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+5 0 10^3 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+1 0 10^2c+8 0 10^2d+4 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+5 0 10^3 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+1 0 10^2c+8 0 10^2d+4 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+5 0 10^3 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+6 01100 10^2c+1 0 10^2d+5 0 10^3 0^inf
                        chain_step(0, "b+3"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b+2 011100101 B> 10^2c+1 0 10^2d+5 0 10^3 0^inf
                        rule_step(5, &[("a", "c")]),
                        rule_step(6, &[("a", "c+1")]),
                        rule_step(7, &[("a", "c+2")]),
                        // 0^inf 1100101 0001^a 010 0001^b+1 010 <B 0100 10^2c+7 0 10^2d+2 0 10^3 0^inf
                        chain_step(1, "b+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2 0 10^2c+7 0 10^2d+2 0 10^3 0^inf
                        chain_step(0, "b+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 B> 10^2c+8 0 10^2d+2 0 10^3 0^inf
                        chain_step(0, "c+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 010 B> 10^2d+3 0 10^3 0^inf
                        rule_step(4, &[("a", "d")]),
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+2 001100101 B> 10^2d+5 0^inf
                        rule_step(3, &[("a", "2d+3")]),
                        base_step(165),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+2 01010 <B 0 10^4 0 10^2d+4 0^inf
                        chain_step(2, "c+2"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b 01010 <B 0100 10^2c+8 0 10^2d+4 0^inf
                        chain_step(2, "b"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b+1 0 10^2c+8 0 10^2d+4 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+1 0 10^2c+8 0 10^2d+4 0^inf
                    ]),
                },
                // 68: 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+4 0 10^e+1 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+1 0 10^2c+7 0 10^2d+1 0 10^e+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+4 0 10^e+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+1 0 10^2c+7 0 10^2d+1 0 10^e+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+4 0 10^e+1 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+6 01100 10^2c+1 0 10^2d+4 0 10^e+1 0^inf
                        chain_step(0, "b+3"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b+2 011100101 B> 10^2c+1 0 10^2d+4 0 10^e+1 0^inf
                        rule_step(5, &[("a", "c")]),
                        rule_step(6, &[("a", "c+1")]),
                        rule_step(7, &[("a", "c+2")]),
                        // 0^inf 1100101 0001^a 010 0001^b+1 010 <B 0100 10^2c+7 0 10^2d+1 0 10^e+1 0^inf
                        chain_step(1, "b+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2 0 10^2c+7 0 10^2d+1 0 10^e+1 0^inf
                        chain_step(0, "b+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 B> 10^2c+8 0 10^2d+1 0 10^e+1 0^inf
                        chain_step(0, "c+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 010 B> 10^2d+2 0 10^e+1 0^inf
                        chain_step(0, "d+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 010 0001^d 010 B> 10^e+2 0^inf
                        rule_step(3, &[("a", "e")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 010 0001^d 01010 <B 0100 10^e+1 0^inf
                        chain_step(2, "d"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 01010 <B 0100 10^2d+1 0 10^e+1 0^inf
                        chain_step(2, "c+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b 01010 <B 0100 10^2c+7 0 10^2d+1 0 10^e+1 0^inf
                        chain_step(2, "b"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b+1 0 10^2c+7 0 10^2d+1 0 10^e+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+1 0 10^2c+7 0 10^2d+1 0 10^e+1 0^inf
                    ]),
                },
                // 69: 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+5 0 10^2e+5 0 10^f+1 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 01100 10^2c+3 0 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+5 0 10^2e+5 0 10^f+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 01100 10^2c+3 0 10^2d+7 0 10^2e+1 0 10^f+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+5 0 10^2e+5 0 10^f+1 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+6 01100 10^2c+1 0 10^2d+5 0 10^2e+5 0 10^f+1 0^inf
                        chain_step(0, "b+3"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b+2 011100101 B> 10^2c+1 0 10^2d+5 0 10^2e+5 0 10^f+1 0^inf
                        rule_step(5, &[("a", "c")]),
                        rule_step(6, &[("a", "c+1")]),
                        rule_step(7, &[("a", "c+2")]),
                        // 0^inf 1100101 0001^a 010 0001^b+1 010 <B 0100 10^2c+7 0 10^2d+2 0 10^2e+5 0 10^f+1 0^inf
                        chain_step(1, "b+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2 0 10^2c+7 0 10^2d+2 0 10^2e+5 0 10^f+1 0^inf
                        chain_step(0, "b+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 B> 10^2c+8 0 10^2d+2 0 10^2e+5 0 10^f+1 0^inf
                        chain_step(0, "c+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 010 B> 10^2d+3 0 10^2e+5 0 10^f+1 0^inf
                        rule_step(4, &[("a", "d")]),
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        rule_step(7, &[("a", "d+2")]),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+2 010 <B 0100 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(1, "c+2"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 B> 10^2c+4 0 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 010 B> 10^2d+8 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(0, "d+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 010 0001^d+3 010 B> 10^2e+2 0 10^f+1 0^inf
                        chain_step(0, "e+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 010 0001^d+3 010 0001^e 010 B> 10^f+2 0^inf
                        rule_step(3, &[("a", "f")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 010 0001^d+3 010 0001^e 01010 <B 0100 10^f+1 0^inf
                        chain_step(2, "e"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 010 0001^d+3 01010 <B 0100 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "d+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 01010 <B 0100 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 011100101 0001^b 01010 <B 0 10^2 01100 10^2c+3 0 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "b"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b+2 01100 10^2c+3 0 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 01100 10^2c+3 0 10^2d+7 0 10^2e+1 0 10^f+1 0^inf
                    ]),
                },
                // 70: 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+4 01100 10^2d+1 0 10^2e+5 0 10^2f+5 0 10^g+1 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+4 01100 10^2c+3 0 10^2d+3 0 10^2e+7 0 10^2f+1 0 10^g+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+4 01100 10^2d+1 0 10^2e+5 0 10^2f+5 0 10^g+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+4 01100 10^2c+3 0 10^2d+3 0 10^2e+7 0 10^2f+1 0 10^g+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+4 01100 10^2d+1 0 10^2e+5 0 10^2f+5 0 10^g+1 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+2 01100 10^2c+4 01100 10^2d+1 0 10^2e+5 0 10^2f+5 0 10^g+1 0^inf
                        chain_step(0, "b+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 B> 10^2c+4 01100 10^2d+1 0 10^2e+5 0 10^2f+5 0 10^g+1 0^inf
                        chain_step(0, "c+2"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 0001^c+1 011100101 B> 10^2d+1 0 10^2e+5 0 10^2f+5 0 10^g+1 0^inf
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        rule_step(7, &[("a", "d+2")]),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 0001^c 010 <B 0100 10^2d+7 0 10^2e+2 0 10^2f+5 0 10^g+1 0^inf
                        chain_step(1, "c"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 B> 10^2c+4 0 10^2d+7 0 10^2e+2 0 10^2f+5 0 10^g+1 0^inf
                        chain_step(0, "c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 B> 10^2d+8 0 10^2e+2 0 10^2f+5 0 10^g+1 0^inf
                        chain_step(0, "d+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+3 010 B> 10^2e+3 0 10^2f+5 0 10^g+1 0^inf
                        rule_step(4, &[("a", "e")]),
                        rule_step(5, &[("a", "e")]),
                        rule_step(6, &[("a", "e+1")]),
                        rule_step(7, &[("a", "e+2")]),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+2 010 <B 0100 10^2e+7 0 10^2f+1 0 10^g+1 0^inf
                        chain_step(1, "d+2"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 011100101 B> 10^2d+4 0 10^2e+7 0 10^2f+1 0 10^g+1 0^inf
                        chain_step(0, "d+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 011100101 0001^d+1 010 B> 10^2e+8 0 10^2f+1 0 10^g+1 0^inf
                        chain_step(0, "e+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 011100101 0001^d+1 010 0001^e+3 010 B> 10^2f+2 0 10^g+1 0^inf
                        chain_step(0, "f+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 011100101 0001^d+1 010 0001^e+3 010 0001^f 010 B> 10^g+2 0^inf
                        rule_step(3, &[("a", "g")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 011100101 0001^d+1 010 0001^e+3 010 0001^f 01010 <B 0100 10^g+1 0^inf
                        chain_step(2, "f"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 011100101 0001^d+1 010 0001^e+3 01010 <B 0100 10^2f+1 0 10^g+1 0^inf
                        chain_step(2, "e+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 011100101 0001^d+1 01010 <B 0100 10^2e+7 0 10^2f+1 0 10^g+1 0^inf
                        chain_step(2, "d+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 01010 <B 0 10^2 01100 10^2d+3 0 10^2e+7 0 10^2f+1 0 10^g+1 0^inf
                        chain_step(2, "c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 0001^b 010 <B 0 10^2 01100 10^2c+4 01100 10^2d+3 0 10^2e+7 0 10^2f+1 0 10^g+1 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+1 01100 10^2c+4 01100 10^2d+3 0 10^2e+7 0 10^2f+1 0 10^g+1 0^inf
                        rule_step(5, &[("a", "b")]),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+4 0 10^2c+4 01100 10^2d+3 0 10^2e+7 0 10^2f+1 0 10^g+1 0^inf
                        chain_step(0, "b+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 B> 10^2c+5 01100 10^2d+3 0 10^2e+7 0 10^2f+1 0 10^g+1 0^inf
                        rule_step(4, &[("a", "c+1")]),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 B> 10^2c+4 0 10^2d+3 0 10^2e+7 0 10^2f+1 0 10^g+1 0^inf
                        chain_step(0, "c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 B> 10^2d+4 0 10^2e+7 0 10^2f+1 0 10^g+1 0^inf
                        chain_step(0, "d+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+1 010 B> 10^2e+8 0 10^2f+1 0 10^g+1 0^inf
                        chain_step(0, "e+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+1 010 0001^e+3 010 B> 10^2f+2 0 10^g+1 0^inf
                        chain_step(0, "f+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+1 010 0001^e+3 010 0001^f 010 B> 10^g+2 0^inf
                        rule_step(3, &[("a", "g")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+1 010 0001^e+3 010 0001^f 01010 <B 0100 10^g+1 0^inf
                        chain_step(2, "f"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+1 010 0001^e+3 01010 <B 0100 10^2f+1 0 10^g+1 0^inf
                        chain_step(2, "e+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+1 01010 <B 0100 10^2e+7 0 10^2f+1 0 10^g+1 0^inf
                        chain_step(2, "d+1"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 01010 <B 0100 10^2d+3 0 10^2e+7 0 10^2f+1 0 10^g+1 0^inf
                        chain_step(2, "c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 01010 <B 0 10^2 01100 10^2c+3 0 10^2d+3 0 10^2e+7 0 10^2f+1 0 10^g+1 0^inf
                        chain_step(2, "b+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+4 01100 10^2c+3 0 10^2d+3 0 10^2e+7 0 10^2f+1 0 10^g+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+4 01100 10^2c+3 0 10^2d+3 0 10^2e+7 0 10^2f+1 0 10^g+1 0^inf
                    ]),
                },
                // 71: 0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2d+5 0 10^2e+4n+1 0 10^2f+1 0 10^g+1 0^inf  -->  0^inf 1100101 B> 10^2a+4n+2 01100 10^2b+4 01100 10^2c+2n+1 0 10^2d+2n+5 0 10^2e+1 0 10^2f+1 0 10^g+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2d+5 0 10^2e+4n+1 0 10^2f+1 0 10^g+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+4n+2 01100 10^2b+4 01100 10^2c+2n+1 0 10^2d+2n+5 0 10^2e+1 0 10^2f+1 0 10^g+1 0^inf").unwrap(),
                    proof: Proof::Inductive {
                        proof_base: vec![],
                        proof_inductive: vec![
                            // 0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2d+5 0 10^2e+4n+5 0 10^2f+1 0 10^g+1 0^inf
                            chain_step(0, "a+1"),
                            base_step(49),
                            // 0^inf 1100101 0001^a 011100101 B> 10^2b+4 01100 10^2c+1 0 10^2d+5 0 10^2e+4n+5 0 10^2f+1 0 10^g+1 0^inf
                            chain_step(0, "b+2"),
                            base_step(49),
                            // 0^inf 1100101 0001^a 011100101 0001^b+1 011100101 B> 10^2c+1 0 10^2d+5 0 10^2e+4n+5 0 10^2f+1 0 10^g+1 0^inf
                            rule_step(5, &[("a", "c")]),
                            rule_step(6, &[("a", "c+1")]),
                            rule_step(7, &[("a", "c+2")]),
                            // 0^inf 1100101 0001^a 011100101 0001^b 010 <B 0100 10^2c+7 0 10^2d+2 0 10^2e+4n+5 0 10^2f+1 0 10^g+1 0^inf
                            chain_step(1, "b"),
                            base_step(146),
                            // 0^inf 1100101 0001^a 1100101 B> 10^2b+4 0 10^2c+7 0 10^2d+2 0 10^2e+4n+5 0 10^2f+1 0 10^g+1 0^inf
                            chain_step(0, "b+2"),
                            base_step(5),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 010 B> 10^2c+8 0 10^2d+2 0 10^2e+4n+5 0 10^2f+1 0 10^g+1 0^inf
                            chain_step(0, "c+4"),
                            base_step(5),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+3 010 B> 10^2d+3 0 10^2e+4n+5 0 10^2f+1 0 10^g+1 0^inf
                            rule_step(4, &[("a", "d")]),
                            rule_step(5, &[("a", "d")]),
                            rule_step(6, &[("a", "d+1")]),
                            rule_step(7, &[("a", "d+2")]),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+2 010 <B 0100 10^2d+7 0 10^2e+4n+1 0 10^2f+1 0 10^g+1 0^inf
                            chain_step(1, "c+2"),
                            base_step(22),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 B> 10^2c+4 0 10^2d+7 0 10^2e+4n+1 0 10^2f+1 0 10^g+1 0^inf
                            chain_step(0, "c+2"),
                            base_step(5),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 B> 10^2d+8 0 10^2e+4n+1 0 10^2f+1 0 10^g+1 0^inf
                            chain_step(0, "d+4"),
                            base_step(5),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+3 010 B> 10^2e+4n+2 0 10^2f+1 0 10^g+1 0^inf
                            chain_step(0, "e+2n+1"),
                            base_step(5),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+3 010 0001^e+2n 010 B> 10^2f+2 0 10^g+1 0^inf
                            chain_step(0, "f+1"),
                            base_step(5),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+3 010 0001^e+2n 010 0001^f 010 B> 10^g+2 0^inf
                            rule_step(3, &[("a", "g")]),
                            base_step(9),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+3 010 0001^e+2n 010 0001^f 01010 <B 0100 10^g+1 0^inf
                            chain_step(2, "f"),
                            base_step(9),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+3 010 0001^e+2n 01010 <B 0100 10^2f+1 0 10^g+1 0^inf
                            chain_step(2, "e+2n"),
                            base_step(9),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 010 0001^d+3 01010 <B 0100 10^2e+4n+1 0 10^2f+1 0 10^g+1 0^inf
                            chain_step(2, "d+3"),
                            base_step(9),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 011100101 0001^c+1 01010 <B 0100 10^2d+7 0 10^2e+4n+1 0 10^2f+1 0 10^g+1 0^inf
                            chain_step(2, "c+1"),
                            base_step(39),
                            // 0^inf 1100101 0001^a 1100101 0001^b+1 01010 <B 0 10^2 01100 10^2c+3 0 10^2d+7 0 10^2e+4n+1 0 10^2f+1 0 10^g+1 0^inf
                            chain_step(2, "b+1"),
                            base_step(39),
                            // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+4 01100 10^2c+3 0 10^2d+7 0 10^2e+4n+1 0 10^2f+1 0 10^g+1 0^inf
                            chain_step(1, "a"),
                            base_step(186),
                            // 0^inf 1100101 B> 10^2a+6 01100 10^2b+4 01100 10^2c+3 0 10^2d+7 0 10^2e+4n+1 0 10^2f+1 0 10^g+1 0^inf
                            induction_step(&[("a", "a+2"), ("b", "b"), ("c", "c+1"), ("d", "d+1"), ("e", "e"), ("f", "f"), ("g", "g")]),
                            // 0^inf 1100101 B> 10^2a+4n+6 01100 10^2b+4 01100 10^2c+2n+3 0 10^2d+2n+7 0 10^2e+1 0 10^2f+1 0 10^g+1 0^inf
                        ],
                    },
                },
                // 72: 0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2d+5 0100 10^2e+1 0 10^f+2 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+8 0 10^2d+2e+5 0 10^f+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2d+5 0100 10^2e+1 0 10^f+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+8 0 10^2d+2e+5 0 10^f+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2d+5 0100 10^2e+1 0 10^f+2 0^inf
                        chain_step(0, "a+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+4 01100 10^2c+1 0 10^2d+5 0100 10^2e+1 0 10^f+2 0^inf
                        chain_step(0, "b+2"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 011100101 0001^b+1 011100101 B> 10^2c+1 0 10^2d+5 0100 10^2e+1 0 10^f+2 0^inf
                        rule_step(5, &[("a", "c")]),
                        rule_step(6, &[("a", "c+1")]),
                        rule_step(7, &[("a", "c+2")]),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 <B 0100 10^2c+7 0 10^2d+2 0100 10^2e+1 0 10^f+2 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+4 0 10^2c+7 0 10^2d+2 0100 10^2e+1 0 10^f+2 0^inf
                        chain_step(0, "b+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 B> 10^2c+8 0 10^2d+2 0100 10^2e+1 0 10^f+2 0^inf
                        chain_step(0, "c+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+3 010 B> 10^2d+3 0100 10^2e+1 0 10^f+2 0^inf
                        rule_step(4, &[("a", "d")]),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+3 011100101 B> 10^2d+1 00 10^2e+1 0 10^f+2 0^inf
                        chain_step(0, "d"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+3 011100101 0001^d 0101 B> 10^2e+1 0 10^f+2 0^inf
                        chain_step(0, "e"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+3 011100101 0001^d 0101 0001^e 010 <B 00 10^f+1 0^inf
                        chain_step(1, "e"),
                        base_step(4),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+3 011100101 0001^d 010 <B 01100 10^2e 0 10^f+1 0^inf
                        chain_step(1, "d"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+3 1100101 B> 10^2d+3 1100 10^2e 0 10^f+1 0^inf
                        chain_step(0, "d+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+3 1100101 0001^d+1 010 <B 0 10^2e+1 0 10^f+1 0^inf
                        chain_step(1, "d+1"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+2 001100101 B> 10^2d+2e+6 0 10^f+1 0^inf
                        chain_step(0, "d+e+3"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+2 001100101 0001^d+e+2 010 B> 10^f+2 0^inf
                        rule_step(3, &[("a", "f")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+2 001100101 0001^d+e+2 01010 <B 0100 10^f+1 0^inf
                        chain_step(2, "d+e+2"),
                        base_step(165),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+2 01010 <B 0 10^4 0 10^2d+2e+5 0 10^f+1 0^inf
                        chain_step(2, "c+2"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 01010 <B 0100 10^2c+8 0 10^2d+2e+5 0 10^f+1 0^inf
                        chain_step(2, "b+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+3 0 10^2c+8 0 10^2d+2e+5 0 10^f+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+8 0 10^2d+2e+5 0 10^f+1 0^inf
                    ]),
                },
                // 73: 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0100 10^2c+1 0 10^d+2 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+2c+5 0 10^d+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b+2 0100 10^2c+1 0 10^d+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+2c+5 0 10^d+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0100 10^2c+1 0 10^d+2 0^inf
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 0100 10^2c+1 0 10^d+2 0^inf
                        rule_step(4, &[("a", "b")]),
                        // 0^inf 1100101 0001^a+1 011100101 B> 10^2b+1 00 10^2c+1 0 10^d+2 0^inf
                        chain_step(0, "b"),
                        base_step(6),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 0101 B> 10^2c+1 0 10^d+2 0^inf
                        chain_step(0, "c"),
                        base_step(6),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 0101 0001^c 010 <B 00 10^d+1 0^inf
                        chain_step(1, "c"),
                        base_step(4),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 010 <B 01100 10^2c 0 10^d+1 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a+1 1100101 B> 10^2b+3 1100 10^2c 0 10^d+1 0^inf
                        chain_step(0, "b+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a+1 1100101 0001^b+1 010 <B 0 10^2c+1 0 10^d+1 0^inf
                        chain_step(1, "b+1"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+2c+6 0 10^d+1 0^inf
                        chain_step(0, "b+c+3"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 001100101 0001^b+c+2 010 B> 10^d+2 0^inf
                        rule_step(3, &[("a", "d")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 001100101 0001^b+c+2 01010 <B 0100 10^d+1 0^inf
                        chain_step(2, "b+c+2"),
                        base_step(165),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^4 0 10^2b+2c+5 0 10^d+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+2c+5 0 10^d+1 0^inf
                    ]),
                },
                // 74: 0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2d+5 0100 10^e+2 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+8 01100 10^2d 1100 10^e+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2d+5 0100 10^e+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+8 01100 10^2d 1100 10^e+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 01100 10^2b+4 01100 10^2c+1 0 10^2d+5 0100 10^e+2 0^inf
                        chain_step(0, "a+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+4 01100 10^2c+1 0 10^2d+5 0100 10^e+2 0^inf
                        chain_step(0, "b+2"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 011100101 0001^b+1 011100101 B> 10^2c+1 0 10^2d+5 0100 10^e+2 0^inf
                        rule_step(5, &[("a", "c")]),
                        rule_step(6, &[("a", "c+1")]),
                        rule_step(7, &[("a", "c+2")]),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 <B 0100 10^2c+7 0 10^2d+2 0100 10^e+2 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+4 0 10^2c+7 0 10^2d+2 0100 10^e+2 0^inf
                        chain_step(0, "b+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 B> 10^2c+8 0 10^2d+2 0100 10^e+2 0^inf
                        chain_step(0, "c+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+3 010 B> 10^2d+3 0100 10^e+2 0^inf
                        chain_step(0, "d+1"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+3 010 0001^d+1 010 <B 000 10^e+2 0^inf
                        chain_step(1, "d+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+3 011100101 B> 10^2d+1 00 10^e+2 0^inf
                        chain_step(0, "d"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+3 011100101 0001^d 0101 B> 10^e+2 0^inf
                        rule_step(3, &[("a", "e")]),
                        base_step(4),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+3 011100101 0001^d 01010 <B 01100 10^e+1 0^inf
                        chain_step(2, "d"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+3 01010 <B 0 10^2 01100 10^2d 1100 10^e+1 0^inf
                        chain_step(2, "c+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 01010 <B 0100 10^2c+8 01100 10^2d 1100 10^e+1 0^inf
                        chain_step(2, "b+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+3 0 10^2c+8 01100 10^2d 1100 10^e+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+8 01100 10^2d 1100 10^e+1 0^inf
                    ]),
                },
                // 75: 0^inf 1100101 B> 10^2a+4 0 10^2b+2 01001100 10^2c+2 1100 10^d 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+2c+d+9 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b+2 01001100 10^2c+2 1100 10^d 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+2c+d+9 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b+2 01001100 10^2c+2 1100 10^d 0^inf
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 01001100 10^2c+2 1100 10^d 0^inf
                        rule_step(4, &[("a", "b")]),
                        // 0^inf 1100101 0001^a+1 011100101 B> 10^2b+1 001100 10^2c+2 1100 10^d 0^inf
                        chain_step(0, "b"),
                        base_step(24),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 0101100101 B> 10^2c+1 1100 10^d 0^inf
                        chain_step(0, "c"),
                        base_step(22),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 0101100101 0001^c 010 <B 0 10^d+1 0^inf
                        chain_step(1, "c"),
                        base_step(102),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 010 <B 01100 10^2c+d+4 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a+1 1100101 B> 10^2b+3 1100 10^2c+d+4 0^inf
                        chain_step(0, "b+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a+1 1100101 0001^b+1 010 <B 0 10^2c+d+5 0^inf
                        chain_step(1, "b+1"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+2c+d+10 0^inf
                        rule_step(3, &[("a", "2b+2c+d+8")]),
                        base_step(165),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^4 0 10^2b+2c+d+9 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+2c+d+9 0^inf
                    ]),
                },
                // 76: 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 01100 10^2c+2 1100 10^d 0^inf  -->  0^inf 1100101 B> 10^2a+8 0 10^2b+6 1100 10^2c+d+4 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 01100 10^2c+2 1100 10^d 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+8 0 10^2b+6 1100 10^2c+d+4 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b+2 0 10^3 01100 10^2c+2 1100 10^d 0^inf
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 0 10^3 01100 10^2c+2 1100 10^d 0^inf
                        rule_step(4, &[("a", "b")]),
                        rule_step(5, &[("a", "b")]),
                        rule_step(6, &[("a", "b+1")]),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+5 001100 10^2c+2 1100 10^d 0^inf
                        chain_step(0, "b+2"),
                        base_step(24),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 0101100101 B> 10^2c+1 1100 10^d 0^inf
                        chain_step(0, "c"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 0101100101 0001^c 010 <B 0 10^d+1 0^inf
                        chain_step(1, "c"),
                        base_step(102),
                        // 0^inf 1100101 0001^a 001100101 0001^b+2 010 <B 01100 10^2c+d+4 0^inf
                        chain_step(1, "b+2"),
                        base_step(107),
                        // 0^inf 1100101 0001^a 010 <B 0100 10^2b+7 1100 10^2c+d+4 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+5 0 10^2b+7 1100 10^2c+d+4 0^inf
                        chain_step(0, "a+2"),
                        base_step(6),
                        // 0^inf 1100101 0001^a+2 010 <B 00 10^2b+6 1100 10^2c+d+4 0^inf
                        chain_step(1, "a+2"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+8 0 10^2b+6 1100 10^2c+d+4 0^inf
                    ]),
                },
                // 77: 0^inf 1100101 B> 10^2a+4 01100 10^2b+2 1100 10^6 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+3 0 10^9 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 01100 10^2b+2 1100 10^6 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+3 0 10^9 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 01100 10^2b+2 1100 10^6 0^inf
                        chain_step(0, "a+2"),
                        base_step(49),
                        // 0^inf 1100101 0001^a+1 011100101 B> 10^2b+2 1100 10^6 0^inf
                        chain_step(0, "b+1"),
                        base_step(358),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 010 <B 0100 10^4 0 10^4 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a+1 1100101 B> 10^2b+4 0 10^4 0 10^4 0^inf
                        chain_step(0, "b+2"),
                        base_step(1042),
                        // 0^inf 1100101 0001^a+1 1100101 0001^b 010 <B 0100 10^9 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+4 0 10^9 0^inf
                        chain_step(0, "b+2"),
                        base_step(362),
                        // 0^inf 1100101 0001^a 001100101 0001^b+1 01010 <B 0100 10^9 0^inf
                        chain_step(2, "b+1"),
                        base_step(165),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^4 0 10^2b+3 0 10^9 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+3 0 10^9 0^inf
                    ]),
                },
                // 78: 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+4 01100 10^2d+1 0 10^2e+7 01 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+4 01100 10^2d+7 0 10^2e+2 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+4 01100 10^2d+1 0 10^2e+7 01 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+4 01100 10^2d+7 0 10^2e+2 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+4 01100 10^2d+1 0 10^2e+7 01 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+2 01100 10^2c+4 01100 10^2d+1 0 10^2e+7 01 0^inf
                        chain_step(0, "b+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 B> 10^2c+4 01100 10^2d+1 0 10^2e+7 01 0^inf
                        chain_step(0, "c+2"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 0001^c+1 011100101 B> 10^2d+1 0 10^2e+7 01 0^inf
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        rule_step(7, &[("a", "d+2")]),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 0001^c 010 <B 0100 10^2d+7 0 10^2e+4 01 0^inf
                        chain_step(1, "c"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 B> 10^2c+4 0 10^2d+7 0 10^2e+4 01 0^inf
                        chain_step(0, "c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 B> 10^2d+8 0 10^2e+4 01 0^inf
                        chain_step(0, "d+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+3 010 B> 10^2e+5 01 0^inf
                        rule_step(4, &[("a", "e+1")]),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+3 011100101 B> 10^2e+3 0^inf
                        rule_step(3, &[("a", "2e+1")]),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+3 01010 <B 0 10^2 01100 10^2e+2 0^inf
                        chain_step(2, "d+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 01010 <B 0100 10^2d+8 01100 10^2e+2 0^inf
                        chain_step(2, "c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 0001^b 010 <B 0 10^2 01100 10^2c+3 0 10^2d+8 01100 10^2e+2 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+1 01100 10^2c+3 0 10^2d+8 01100 10^2e+2 0^inf
                        rule_step(5, &[("a", "b")]),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+4 0 10^2c+3 0 10^2d+8 01100 10^2e+2 0^inf
                        chain_step(0, "b+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 B> 10^2c+4 0 10^2d+8 01100 10^2e+2 0^inf
                        chain_step(0, "c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 010 B> 10^2d+9 01100 10^2e+2 0^inf
                        rule_step(4, &[("a", "d+3")]),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 011100101 B> 10^2d+8 0 10^2e+2 0^inf
                        chain_step(0, "d+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 011100101 0001^d+3 010 B> 10^2e+3 0^inf
                        rule_step(3, &[("a", "2e+1")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 011100101 0001^d+3 01010 <B 0100 10^2e+2 0^inf
                        chain_step(2, "d+3"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 01010 <B 0 10^2 01100 10^2d+7 0 10^2e+2 0^inf
                        chain_step(2, "c+1"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 01010 <B 0100 10^2c+4 01100 10^2d+7 0 10^2e+2 0^inf
                        chain_step(2, "b+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+3 0 10^2c+4 01100 10^2d+7 0 10^2e+2 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+4 01100 10^2d+7 0 10^2e+2 0^inf
                    ]),
                },
                // 79: 0^inf 1100101 B> 10^2a+4 0 10^2b+2 01001100 10^2c+3 0 10^d+1 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+7 0 10^3 0 10^2c+1 0 10^d+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b+2 01001100 10^2c+3 0 10^d+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+7 0 10^3 0 10^2c+1 0 10^d+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b+2 01001100 10^2c+3 0 10^d+1 0^inf
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+3 01001100 10^2c+3 0 10^d+1 0^inf
                        rule_step(4, &[("a", "b")]),
                        // 0^inf 1100101 0001^a+1 011100101 B> 10^2b+1 001100 10^2c+3 0 10^d+1 0^inf
                        chain_step(0, "b"),
                        base_step(24),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 0101100101 B> 10^2c+2 0 10^d+1 0^inf
                        chain_step(0, "c+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 0101100101 0001^c 010 B> 10^d+2 0^inf
                        rule_step(3, &[("a", "d")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 0101100101 0001^c 01010 <B 0100 10^d+1 0^inf
                        chain_step(2, "c"),
                        base_step(234),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 11001010001010 B> 10^2c+2 0 10^d+1 0^inf
                        chain_step(0, "c+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 11001010001010 0001^c 010 B> 10^d+2 0^inf
                        rule_step(3, &[("a", "d")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 11001010001010 0001^c 01010 <B 0100 10^d+1 0^inf
                        chain_step(2, "c"),
                        base_step(120),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 010 <B 0 10^2 01100 10^3 0 10^2c+1 0 10^d+1 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a+1 1100101 B> 10^2b+5 01100 10^3 0 10^2c+1 0 10^d+1 0^inf
                        rule_step(6, &[("a", "b+2")]),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+8 0 10^3 0 10^2c+1 0 10^d+1 0^inf
                        chain_step(0, "b+4"),
                        base_step(26),
                        // 0^inf 1100101 0001^a 001100101 0001^b+3 0100001010 B> 10^2c+2 0 10^d+1 0^inf
                        chain_step(0, "c+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 001100101 0001^b+3 0100001010 0001^c 010 B> 10^d+2 0^inf
                        rule_step(3, &[("a", "d")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 001100101 0001^b+3 0100001010 0001^c 01010 <B 0100 10^d+1 0^inf
                        chain_step(2, "c"),
                        base_step(90),
                        // 0^inf 1100101 0001^a 001100101 0001^b+3 01010 <B 0100 10^3 0 10^2c+1 0 10^d+1 0^inf
                        chain_step(2, "b+3"),
                        base_step(165),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^4 0 10^2b+7 0 10^3 0 10^2c+1 0 10^d+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+7 0 10^3 0 10^2c+1 0 10^d+1 0^inf
                    ]),
                },
                // 80: 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2 0 10^2d+5 0 10^e+1 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+3 0 10^7 0 10^2d+1 0 10^e+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2 0 10^2d+5 0 10^e+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+3 0 10^7 0 10^2d+1 0 10^e+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2 0 10^2d+5 0 10^e+1 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+1 1100 10^2c+4 0 10^2 0 10^2d+5 0 10^e+1 0^inf
                        chain_step(0, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 010 0001^b 010 <B 0 10^2c+5 0 10^2 0 10^2d+5 0 10^e+1 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2c+4 0 10^2 0 10^2d+5 0 10^e+1 0^inf
                        chain_step(0, "b+c+2"),
                        base_step(746),
                        // 0^inf 1100101 0001^a 011100101 0001^b+c 010 <B 0100 10^7 0 10^2d+1 0 10^e+1 0^inf
                        chain_step(1, "b+c"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+2c+4 0 10^7 0 10^2d+1 0 10^e+1 0^inf
                        chain_step(0, "b+c+2"),
                        base_step(42),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 0001^3 010 B> 10^2d+2 0 10^e+1 0^inf
                        chain_step(0, "d+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 0001^3 010 0001^d 010 B> 10^e+2 0^inf
                        rule_step(3, &[("a", "e")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 0001^3 010 0001^d 01010 <B 0100 10^e+1 0^inf
                        chain_step(2, "d"),
                        base_step(234),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 01010 <B 0100 10^7 0 10^2d+1 0 10^e+1 0^inf
                        chain_step(2, "b+c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+2c+3 0 10^7 0 10^2d+1 0 10^e+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+3 0 10^7 0 10^2d+1 0 10^e+1 0^inf
                    ]),
                },
                // 81: 0^inf 1100101 B> 10^2a+4 01100 10^2b+2 1100 10^c+7 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+3 0 10^9 0 10^c+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 01100 10^2b+2 1100 10^c+7 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+3 0 10^9 0 10^c+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 01100 10^2b+2 1100 10^c+7 0^inf
                        chain_step(0, "a+2"),
                        base_step(49),
                        // 0^inf 1100101 0001^a+1 011100101 B> 10^2b+2 1100 10^c+7 0^inf
                        chain_step(0, "b+1"),
                        base_step(18),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b+1 100101 B> 10^c+6 0^inf
                        rule_step(3, &[("a", "c+4")]),
                        base_step(174),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b 010 <B 0100 10^4 0 10^c+5 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a+1 1100101 B> 10^2b+4 0 10^4 0 10^c+5 0^inf
                        chain_step(0, "b+2"),
                        base_step(1042),
                        // 0^inf 1100101 0001^a+1 1100101 0001^b 010 <B 0100 10^9 0 10^c+1 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+4 0 10^9 0 10^c+1 0^inf
                        chain_step(0, "b+2"),
                        base_step(50),
                        // 0^inf 1100101 0001^a 001100101 0001^b+1 010 0001^4 010 B> 10^c+2 0^inf
                        rule_step(3, &[("a", "c")]),
                        base_step(306),
                        // 0^inf 1100101 0001^a 001100101 0001^b+1 01010 <B 0100 10^9 0 10^c+1 0^inf
                        chain_step(2, "b+1"),
                        base_step(165),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^4 0 10^2b+3 0 10^9 0 10^c+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+3 0 10^9 0 10^c+1 0^inf
                    ]),
                },
                // 82: 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+2 0 10^2d+4 01 0^inf  -->  0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+2 0 10^2d+4 01 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+2 0 10^2d+4 01 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2c+2 01100 10^2d+2 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+2 0 10^2d+4 01 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+1 1100 10^2c+2 0 10^2d+4 01 0^inf
                        chain_step(0, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 010 0001^b 010 <B 0 10^2c+3 0 10^2d+4 01 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2c+2 0 10^2d+4 01 0^inf
                        chain_step(0, "b+c+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b+c 010 B> 10^2d+5 01 0^inf
                        rule_step(4, &[("a", "d+1")]),
                        // 0^inf 1100101 0001^a 011100101 0001^b+c 011100101 B> 10^2d+3 0^inf
                        rule_step(3, &[("a", "2d+1")]),
                        base_step(39),
                        // 0^inf 1100101 0001^a 011100101 0001^b+c 01010 <B 0 10^2 01100 10^2d+2 0^inf
                        chain_step(2, "b+c"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b+2c+2 01100 10^2d+2 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2c+2 01100 10^2d+2 0^inf
                    ]),
                },
                // 83: 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+2 01100 10^d+2 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+2 01100 10^2c+2 01100 10^d+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+2 01100 10^d+2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+2 01100 10^2c+2 01100 10^d+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+2 01100 10^d+2 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+2 01100 10^2c+2 01100 10^d+2 0^inf
                        chain_step(0, "b+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 B> 10^2c+2 01100 10^d+2 0^inf
                        chain_step(0, "c+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 0001^c 011100101 B> 10^d+2 0^inf
                        rule_step(3, &[("a", "d")]),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 0001^c 01010 <B 0 10^2 01100 10^d+1 0^inf
                        chain_step(2, "c"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 0001^b 01010 <B 0 10^2 01100 10^2c+2 01100 10^d+1 0^inf
                        chain_step(2, "b"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 01010 <B 0100 10^2b+2 01100 10^2c+2 01100 10^d+1 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a 0 10^2b+2 01100 10^2c+2 01100 10^d+1 0^inf
                    ]),
                },
                // 84: 0^inf 1100101 B> 10^2a+2 0 10^2b+2 001100 10^2c+2 01100 10^d+1 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+7 0 10^d+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+2 001100 10^2c+2 01100 10^d+1 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+7 0 10^d+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+2 001100 10^2c+2 01100 10^d+1 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+3 001100 10^2c+2 01100 10^d+1 0^inf
                        chain_step(0, "b+1"),
                        base_step(24),
                        // 0^inf 1100101 0001^a 010 0001^b+1 0101100101 B> 10^2c+1 01100 10^d+1 0^inf
                        chain_step(0, "c"),
                        base_step(6),
                        // 0^inf 1100101 0001^a 010 0001^b+1 0101100101 0001^c 010 <B 0100 10^d+1 0^inf
                        chain_step(1, "c"),
                        base_step(102),
                        // 0^inf 1100101 0001^a 010 0001^b+1 010 <B 01100 10^2c+4 0 10^d+1 0^inf
                        chain_step(1, "b+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+1 1100 10^2c+4 0 10^d+1 0^inf
                        chain_step(0, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 <B 0 10^2c+5 0 10^d+1 0^inf
                        chain_step(1, "b"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+2c+8 0 10^d+1 0^inf
                        chain_step(0, "b+c+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+3 010 B> 10^d+2 0^inf
                        rule_step(3, &[("a", "d")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+3 01010 <B 0100 10^d+1 0^inf
                        chain_step(2, "b+c+3"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+2c+7 0 10^d+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+7 0 10^d+1 0^inf
                    ]),
                },
                // 85: 0^inf 1100101 B> 10^2a+4 0 10^2b 1100 10^2c+2 0 10^2d+2 0 10^2 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+2c+7 0 10^2d+2 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+4 0 10^2b 1100 10^2c+2 0 10^2d+2 0 10^2 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+2c+7 0 10^2d+2 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+4 0 10^2b 1100 10^2c+2 0 10^2d+2 0 10^2 0^inf
                        chain_step(0, "a+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 010 B> 10^2b+1 1100 10^2c+2 0 10^2d+2 0 10^2 0^inf
                        chain_step(0, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a+1 010 0001^b 010 <B 0 10^2c+3 0 10^2d+2 0 10^2 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a+1 011100101 B> 10^2b+2c+2 0 10^2d+2 0 10^2 0^inf
                        chain_step(0, "b+c+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b+c 010 B> 10^2d+3 0 10^2 0^inf
                        rule_step(4, &[("a", "d")]),
                        rule_step(5, &[("a", "d")]),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b+c 1100101 B> 10^2d+3 0^inf
                        rule_step(3, &[("a", "2d+1")]),
                        base_step(39),
                        // 0^inf 1100101 0001^a+1 011100101 0001^b+c 010 <B 0 10^2 01100 10^2d+2 0^inf
                        chain_step(1, "b+c"),
                        base_step(146),
                        // 0^inf 1100101 0001^a+1 1100101 B> 10^2b+2c+5 01100 10^2d+2 0^inf
                        rule_step(6, &[("a", "b+c+2")]),
                        // 0^inf 1100101 0001^a 001100101 B> 10^2b+2c+8 0 10^2d+2 0^inf
                        chain_step(0, "b+c+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 001100101 0001^b+c+3 010 B> 10^2d+3 0^inf
                        rule_step(3, &[("a", "2d+1")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 001100101 0001^b+c+3 01010 <B 0100 10^2d+2 0^inf
                        chain_step(2, "b+c+3"),
                        base_step(165),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^4 0 10^2b+2c+7 0 10^2d+2 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+3 0 10^2b+2c+7 0 10^2d+2 0^inf
                    ]),
                },
                // 86: 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+5 0 10^4 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 01100 10^2c+3 0 10^2d+7 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+5 0 10^4 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 01100 10^2c+3 0 10^2d+7 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+5 01100 10^2c+1 0 10^2d+5 0 10^4 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+6 01100 10^2c+1 0 10^2d+5 0 10^4 0^inf
                        chain_step(0, "b+3"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b+2 011100101 B> 10^2c+1 0 10^2d+5 0 10^4 0^inf
                        rule_step(5, &[("a", "c")]),
                        rule_step(6, &[("a", "c+1")]),
                        rule_step(7, &[("a", "c+2")]),
                        // 0^inf 1100101 0001^a 010 0001^b+1 010 <B 0100 10^2c+7 0 10^2d+2 0 10^4 0^inf
                        chain_step(1, "b+1"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2 0 10^2c+7 0 10^2d+2 0 10^4 0^inf
                        chain_step(0, "b+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 B> 10^2c+8 0 10^2d+2 0 10^4 0^inf
                        chain_step(0, "c+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+3 010 B> 10^2d+3 0 10^4 0^inf
                        rule_step(4, &[("a", "d")]),
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        rule_step(7, &[("a", "d+2")]),
                        // 0^inf 1100101 0001^a 011100101 0001^b 010 0001^c+2 010 <B 0100 10^2d+7 0^inf
                        chain_step(1, "c+2"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 B> 10^2c+4 0 10^2d+7 0^inf
                        chain_step(0, "c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 010 B> 10^2d+8 0^inf
                        rule_step(3, &[("a", "2d+6")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 011100101 0001^b 011100101 0001^c+1 01010 <B 0100 10^2d+7 0^inf
                        chain_step(2, "c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 011100101 0001^b 01010 <B 0 10^2 01100 10^2c+3 0 10^2d+7 0^inf
                        chain_step(2, "b"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b+2 01100 10^2c+3 0 10^2d+7 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2 01100 10^2c+3 0 10^2d+7 0^inf
                    ]),
                },
                // 87: 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+4 01100 10^2d+1 0 10^e+4 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+3 0 10^2d+7 0 10^e+1 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+4 01100 10^2d+1 0 10^e+4 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+3 0 10^2d+7 0 10^e+1 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b+1 01100 10^2c+4 01100 10^2d+1 0 10^e+4 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+2 01100 10^2c+4 01100 10^2d+1 0 10^e+4 0^inf
                        chain_step(0, "b+1"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 B> 10^2c+4 01100 10^2d+1 0 10^e+4 0^inf
                        chain_step(0, "c+2"),
                        base_step(49),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 0001^c+1 011100101 B> 10^2d+1 0 10^e+4 0^inf
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        rule_step(7, &[("a", "d+2")]),
                        // 0^inf 1100101 0001^a 010 0001^b 011100101 0001^c 010 <B 0100 10^2d+7 0 10^e+1 0^inf
                        chain_step(1, "c"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 B> 10^2c+4 0 10^2d+7 0 10^e+1 0^inf
                        chain_step(0, "c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 B> 10^2d+8 0 10^e+1 0^inf
                        chain_step(0, "d+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+3 010 B> 10^e+2 0^inf
                        rule_step(3, &[("a", "e")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 010 0001^d+3 01010 <B 0100 10^e+1 0^inf
                        chain_step(2, "d+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 010 0001^b 1100101 0001^c+1 01010 <B 0100 10^2d+7 0 10^e+1 0^inf
                        chain_step(2, "c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 0001^b 010 <B 0 10^2 01100 10^2c+3 0 10^2d+7 0 10^e+1 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+1 01100 10^2c+3 0 10^2d+7 0 10^e+1 0^inf
                        rule_step(5, &[("a", "b")]),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+4 0 10^2c+3 0 10^2d+7 0 10^e+1 0^inf
                        chain_step(0, "b+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 B> 10^2c+4 0 10^2d+7 0 10^e+1 0^inf
                        chain_step(0, "c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 010 B> 10^2d+8 0 10^e+1 0^inf
                        chain_step(0, "d+4"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 010 0001^d+3 010 B> 10^e+2 0^inf
                        rule_step(3, &[("a", "e")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 010 0001^d+3 01010 <B 0100 10^e+1 0^inf
                        chain_step(2, "d+3"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 010 0001^c+1 01010 <B 0100 10^2d+7 0 10^e+1 0^inf
                        chain_step(2, "c+1"),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+1 01010 <B 0100 10^2c+3 0 10^2d+7 0 10^e+1 0^inf
                        chain_step(2, "b+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+3 0 10^2c+3 0 10^2d+7 0 10^e+1 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+3 0 10^2c+3 0 10^2d+7 0 10^e+1 0^inf
                    ]),
                },
                // 88: 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2d+2 0 10^3 0^inf  -->  0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2c+4 0 10^2d+4 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2d+2 0 10^3 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2c+4 0 10^2d+4 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2d+2 0 10^3 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+1 1100 10^2c+4 0 10^2d+2 0 10^3 0^inf
                        chain_step(0, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 010 0001^b 010 <B 010 10^2c+4 0 10^2d+2 0 10^3 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2c+4 0 10^2d+2 0 10^3 0^inf
                        chain_step(0, "b+c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b+c+1 010 B> 10^2d+3 0 10^3 0^inf
                        rule_step(4, &[("a", "d")]),
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        // 0^inf 1100101 0001^a 011100101 0001^b+c 001100101 B> 10^2d+5 0^inf
                        rule_step(3, &[("a", "2d+3")]),
                        base_step(165),
                        // 0^inf 1100101 0001^a 011100101 0001^b+c 01010 <B 0 10^4 0 10^2d+4 0^inf
                        chain_step(2, "b+c"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 01010 <B 0 10^2 01100 10^2b+2c+4 0 10^2d+4 0^inf
                        chain_step(2, "a"),
                        base_step(593),
                        // 0^inf 1100101 B> 10^8 0 10^2a+1 01100 10^2b+2c+4 0 10^2d+4 0^inf
                    ]),
                },
                // 89: 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2d+2 0 10^4 0^inf  -->  0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+3 0 10^2d+7 0^inf
                Rule {
                    init_config: Config::from_str("0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2d+2 0 10^4 0^inf").unwrap(),
                    final_config: Config::from_str("0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+3 0 10^2d+7 0^inf").unwrap(),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^2a+2 0 10^2b 1100 10^2c+4 0 10^2d+2 0 10^4 0^inf
                        chain_step(0, "a+1"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 010 B> 10^2b+1 1100 10^2c+4 0 10^2d+2 0 10^4 0^inf
                        chain_step(0, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 010 0001^b 010 <B 0 10^2c+5 0 10^2d+2 0 10^4 0^inf
                        chain_step(1, "b"),
                        base_step(22),
                        // 0^inf 1100101 0001^a 011100101 B> 10^2b+2c+4 0 10^2d+2 0 10^4 0^inf
                        chain_step(0, "b+c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 011100101 0001^b+c+1 010 B> 10^2d+3 0 10^4 0^inf
                        rule_step(4, &[("a", "d")]),
                        rule_step(5, &[("a", "d")]),
                        rule_step(6, &[("a", "d+1")]),
                        rule_step(7, &[("a", "d+2")]),
                        // 0^inf 1100101 0001^a 011100101 0001^b+c 010 <B 0100 10^2d+7 0^inf
                        chain_step(1, "b+c"),
                        base_step(146),
                        // 0^inf 1100101 0001^a 1100101 B> 10^2b+2c+4 0 10^2d+7 0^inf
                        chain_step(0, "b+c+2"),
                        base_step(5),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 010 B> 10^2d+8 0^inf
                        rule_step(3, &[("a", "2d+6")]),
                        base_step(9),
                        // 0^inf 1100101 0001^a 1100101 0001^b+c+1 01010 <B 0100 10^2d+7 0^inf
                        chain_step(2, "b+c+1"),
                        base_step(39),
                        // 0^inf 1100101 0001^a 010 <B 0 10^2 01100 10^2b+2c+3 0 10^2d+7 0^inf
                        chain_step(1, "a"),
                        base_step(186),
                        // 0^inf 1100101 B> 10^2a+6 01100 10^2b+2c+3 0 10^2d+7 0^inf
                    ]),
                },
                // 90: 0^inf A> 0^inf  -->  A(39, 39, 269)
                Rule {
                    init_config: Config::from_str("0^inf A> 0^inf").unwrap(),
                    final_config: a("39", "39", "269"),
                    proof: Proof::Simple(vec![
                        // 0^inf A> 0^inf
                        base_step(109),
                        // 0^inf 1100101 B> 10^2 0^inf
                        rule_step(8, &[("a", "0")]),
                        // 0^inf 1100101 B> 10^8 0^inf
                        rule_step(8, &[("a", "6")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0^inf
                        rule_step(9, &[("a", "3"), ("b", "5")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^6 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "2"), ("n", "1")]),
                        // 0^inf 1100101 B> 10^12 0 10^10 0 10^2 0^inf
                        rule_step(11, &[("a", "5"), ("b", "4")]),
                        // 0^inf 1100101 B> 10^16 01100 10^10 0^inf
                        rule_step(12, &[("a", "7"), ("b", "0"), ("c", "8")]),
                        // 0^inf 1100101 B> 10^8 0 10^15 01100 10^9 0^inf
                        rule_step(13, &[("a", "3"), ("b", "7"), ("c", "0"), ("d", "7")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^16 01100 10^8 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "4")]),
                        // 0^inf 1100101 B> 10^24 0 10^22 001100 10^8 0^inf
                        rule_step(14, &[("a", "11"), ("b", "11"), ("c", "5")]),
                        // 0^inf 1100101 B> 10^28 01100 10^25 0 10^3 0 10^6 0^inf
                        rule_step(15, &[("a", "12"), ("b", "0"), ("c", "12")]),
                        // 0^inf 1100101 B> 10^32 0 10^30 00 10^6 0^inf
                        rule_step(16, &[("a", "15"), ("b", "15"), ("c", "4")]),
                        // 0^inf 1100101 B> 10^8 0 10^30 0 10^30 1100 10^5 0^inf
                        rule_step(10, &[("a", "2"), ("b", "14"), ("c", "2"), ("n", "7")]),
                        // 0^inf 1100101 B> 10^36 0 10^58 0 10^2 1100 10^5 0^inf
                        rule_step(17, &[("a", "16"), ("b", "28"), ("c", "4")]),
                        // 0^inf 1100101 B> 10^8 0 10^35 0 10^61 0 10^5 0^inf
                        rule_step(18, &[("a", "3"), ("b", "17"), ("c", "30"), ("d", "4")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^35 0 10^61 0 10^5 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "8")]),
                        // 0^inf 1100101 B> 10^40 0 10^38 0 10^3 0 10^61 0 10^5 0^inf
                        rule_step(19, &[("a", "18"), ("b", "18"), ("c", "30")]),
                        // 0^inf 1100101 B> 10^44 0 10^42 1100 10^60 0 10^4 0^inf
                        rule_step(20, &[("a", "21"), ("b", "21"), ("c", "29"), ("d", "3")]),
                        // 0^inf 1100101 B> 10^8 0 10^43 01100 10^101 0 10^4 0^inf
                        rule_step(21, &[("a", "3"), ("b", "19"), ("c", "50"), ("d", "0")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^39 0 10^107 01 0^inf
                        rule_step(22, &[("a", "3"), ("b", "1"), ("c", "19"), ("d", "50")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^3 0 10^46 01100 10^102 0^inf
                        rule_step(23, &[("a", "3"), ("b", "1"), ("c", "1"), ("d", "21"), ("e", "100")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^3 0 10^9 0 10^44 01100 10^101 0^inf
                        rule_step(24, &[("a", "3"), ("b", "1"), ("c", "1"), ("d", "2"), ("e", "19"), ("f", "100")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4 01100 10^5 0 10^12 01100 10^39 0 10^101 0^inf
                        rule_step(25, &[("a", "3"), ("b", "3"), ("c", "0"), ("d", "2"), ("e", "2"), ("f", "19"), ("g", "97")]),
                        // 0^inf 1100101 B> 10^12 01100 10^9 0 10^4 01100 10^11 0 10^5 0 10^45 0 10^98 0^inf
                        rule_step(15, &[("a", "4"), ("b", "0"), ("c", "4")]),
                        // 0^inf 1100101 B> 10^16 0 10^14 01001100 10^11 0 10^5 0 10^45 0 10^98 0^inf
                        rule_step(26, &[("a", "6"), ("b", "6"), ("c", "4"), ("d", "2"), ("e", "22"), ("f", "97")]),
                        // 0^inf 1100101 B> 10^8 0 10^15 0 10^19 0 10^3 0 10^9 0 10^5 0 10^45 0 10^98 0^inf
                        rule_step(27, &[("a", "3"), ("b", "7"), ("c", "9"), ("d", "1"), ("e", "4"), ("f", "2"), ("g", "22"), ("h", "97")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^15 0 10^19 0 10^3 0 10^9 0 10^5 0 10^45 0 10^98 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "3")]),
                        // 0^inf 1100101 B> 10^20 0 10^18 0 10^3 0 10^19 0 10^3 0 10^9 0 10^5 0 10^45 0 10^98 0^inf
                        rule_step(19, &[("a", "8"), ("b", "8"), ("c", "9")]),
                        // 0^inf 1100101 B> 10^24 0 10^22 1100 10^18 0 10^2 0 10^9 0 10^5 0 10^45 0 10^98 0^inf
                        rule_step(28, &[("a", "11"), ("b", "11"), ("c", "7"), ("d", "0"), ("e", "2"), ("f", "2"), ("g", "22"), ("h", "97")]),
                        // 0^inf 1100101 B> 10^28 01100 10^39 0 10^7 0 10^5 0 10^5 0 10^45 0 10^98 0^inf
                        rule_step(15, &[("a", "12"), ("b", "0"), ("c", "19")]),
                        // 0^inf 1100101 B> 10^32 0 10^44 0 10^4 0 10^5 0 10^5 0 10^45 0 10^98 0^inf
                        rule_step(10, &[("a", "14"), ("b", "21"), ("c", "0"), ("n", "1")]),
                        // 0^inf 1100101 B> 10^36 0 10^48 00 10^5 0 10^5 0 10^45 0 10^98 0^inf
                        rule_step(29, &[("a", "16"), ("b", "23"), ("c", "2"), ("d", "1"), ("e", "20"), ("f", "97")]),
                        // 0^inf 1100101 B> 10^8 0 10^35 0 10^53 0 10^9 0 10^41 0 10^98 0^inf
                        rule_step(30, &[("a", "3"), ("b", "17"), ("c", "26"), ("d", "4"), ("e", "20"), ("f", "97")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^35 0 10^53 0 10^9 0 10^41 0 10^98 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "8")]),
                        // 0^inf 1100101 B> 10^40 0 10^38 0 10^3 0 10^53 0 10^9 0 10^41 0 10^98 0^inf
                        rule_step(19, &[("a", "18"), ("b", "18"), ("c", "26")]),
                        // 0^inf 1100101 B> 10^44 0 10^42 1100 10^52 0 10^8 0 10^41 0 10^98 0^inf
                        rule_step(31, &[("a", "21"), ("b", "21"), ("c", "24"), ("d", "3"), ("e", "18"), ("f", "97")]),
                        // 0^inf 1100101 B> 10^48 01100 10^93 0 10^13 0 10^37 0 10^98 0^inf
                        rule_step(15, &[("a", "22"), ("b", "0"), ("c", "46")]),
                        // 0^inf 1100101 B> 10^52 0 10^98 0 10^10 0 10^37 0 10^98 0^inf
                        rule_step(10, &[("a", "24"), ("b", "48"), ("c", "2"), ("n", "2")]),
                        // 0^inf 1100101 B> 10^60 0 10^106 0 10^2 0 10^37 0 10^98 0^inf
                        rule_step(32, &[("a", "28"), ("b", "52"), ("c", "18"), ("d", "97")]),
                        // 0^inf 1100101 B> 10^64 0 10^147 0 10^97 0^inf
                        rule_step(33, &[("a", "31"), ("b", "73"), ("c", "96")]),
                        // 0^inf 1100101 B> 10^8 0 10^62 0 10^147 0 10^97 0^inf
                        rule_step(10, &[("a", "2"), ("b", "30"), ("c", "3"), ("n", "36")]),
                        // 0^inf 1100101 B> 10^152 0 10^206 0 10^3 0 10^97 0^inf
                        rule_step(34, &[("a", "74"), ("b", "102"), ("c", "95")]),
                        // 0^inf 1100101 B> 10^8 0 10^151 0 10^208 1100 10^96 0^inf
                        rule_step(13, &[("a", "3"), ("b", "75"), ("c", "104"), ("d", "94")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^152 01100 10^303 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "38")]),
                        // 0^inf 1100101 B> 10^160 0 10^158 001100 10^303 0^inf
                    ]),
                },
                // 91: 0^inf D> 0^inf  -->  A(9, 9, 41)
                Rule {
                    init_config: Config::from_str("0^inf D> 0^inf").unwrap(),
                    final_config: a("9", "9", "41"),
                    proof: Proof::Simple(vec![
                        // 0^inf D> 0^inf
                        base_step(168),
                        // 0^inf 1100101 B> 10^3 0^inf
                        rule_step(8, &[("a", "1")]),
                        // 0^inf 1100101 B> 10^8 01 0^inf
                        rule_step(9, &[("a", "3"), ("b", "0")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 01 0^inf
                        rule_step(35, &[("a", "3"), ("b", "1")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4 0^inf
                        rule_step(13, &[("a", "3"), ("b", "3"), ("c", "0"), ("d", "2")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^8 01100 10^3 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "2")]),
                        // 0^inf 1100101 B> 10^16 0 10^14 001100 10^3 0^inf
                        rule_step(14, &[("a", "7"), ("b", "7"), ("c", "0")]),
                        // 0^inf 1100101 B> 10^20 01100 10^17 0 10^3 01 0^inf
                        rule_step(15, &[("a", "8"), ("b", "0"), ("c", "8")]),
                        // 0^inf 1100101 B> 10^24 0 10^22 001 0^inf
                        rule_step(36, &[("a", "11"), ("b", "11")]),
                        // 0^inf 1100101 B> 10^8 0 10^22 0 10^22 11 0^inf
                        rule_step(10, &[("a", "2"), ("b", "10"), ("c", "2"), ("n", "5")]),
                        // 0^inf 1100101 B> 10^28 0 10^42 0 10^2 11 0^inf
                        rule_step(37, &[("a", "12"), ("b", "20")]),
                        // 0^inf 1100101 B> 10^8 0 10^27 0 10^45 0^inf
                        rule_step(33, &[("a", "3"), ("b", "13"), ("c", "44")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^27 0 10^45 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "6")]),
                        // 0^inf 1100101 B> 10^32 0 10^30 0 10^3 0 10^45 0^inf
                        rule_step(34, &[("a", "14"), ("b", "14"), ("c", "43")]),
                        // 0^inf 1100101 B> 10^8 0 10^31 0 10^32 1100 10^44 0^inf
                        rule_step(13, &[("a", "3"), ("b", "15"), ("c", "16"), ("d", "42")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^32 01100 10^75 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "8")]),
                        // 0^inf 1100101 B> 10^40 0 10^38 001100 10^75 0^inf
                    ]),
                },
                // 92: 0^inf E> 0^inf  -->  A(45, 45, 123)
                Rule {
                    init_config: Config::from_str("0^inf E> 0^inf").unwrap(),
                    final_config: a("45", "45", "123"),
                    proof: Proof::Simple(vec![
                        // 0^inf E> 0^inf
                        base_step(350),
                        // 0^inf 1100101 B> 10^5 0^inf
                        rule_step(8, &[("a", "3")]),
                        // 0^inf 1100101 B> 10^8 0 10^3 0^inf
                        rule_step(9, &[("a", "3"), ("b", "2")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^3 0^inf
                        rule_step(38, &[("a", "2"), ("b", "2")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 0 10^8 0^inf
                        rule_step(33, &[("a", "3"), ("b", "3"), ("c", "7")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^7 0 10^8 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "1")]),
                        // 0^inf 1100101 B> 10^12 0 10^10 0 10^3 0 10^8 0^inf
                        rule_step(34, &[("a", "4"), ("b", "4"), ("c", "6")]),
                        // 0^inf 1100101 B> 10^8 0 10^11 0 10^12 1100 10^7 0^inf
                        rule_step(13, &[("a", "3"), ("b", "5"), ("c", "6"), ("d", "5")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^12 01100 10^18 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "3")]),
                        // 0^inf 1100101 B> 10^20 0 10^18 001100 10^18 0^inf
                        rule_step(14, &[("a", "9"), ("b", "9"), ("c", "15")]),
                        // 0^inf 1100101 B> 10^24 01100 10^21 0 10^3 0 10^16 0^inf
                        rule_step(15, &[("a", "10"), ("b", "0"), ("c", "10")]),
                        // 0^inf 1100101 B> 10^28 0 10^26 00 10^16 0^inf
                        rule_step(16, &[("a", "13"), ("b", "13"), ("c", "14")]),
                        // 0^inf 1100101 B> 10^8 0 10^26 0 10^26 1100 10^15 0^inf
                        rule_step(10, &[("a", "2"), ("b", "12"), ("c", "2"), ("n", "6")]),
                        // 0^inf 1100101 B> 10^32 0 10^50 0 10^2 1100 10^15 0^inf
                        rule_step(17, &[("a", "14"), ("b", "24"), ("c", "14")]),
                        // 0^inf 1100101 B> 10^8 0 10^31 0 10^53 0 10^15 0^inf
                        rule_step(18, &[("a", "3"), ("b", "15"), ("c", "26"), ("d", "14")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^31 0 10^53 0 10^15 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "7")]),
                        // 0^inf 1100101 B> 10^36 0 10^34 0 10^3 0 10^53 0 10^15 0^inf
                        rule_step(19, &[("a", "16"), ("b", "16"), ("c", "26")]),
                        // 0^inf 1100101 B> 10^40 0 10^38 1100 10^52 0 10^14 0^inf
                        rule_step(20, &[("a", "19"), ("b", "19"), ("c", "25"), ("d", "13")]),
                        // 0^inf 1100101 B> 10^8 0 10^39 01100 10^89 0 10^14 0^inf
                        rule_step(21, &[("a", "3"), ("b", "17"), ("c", "44"), ("d", "10")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^35 0 10^95 0 10^11 0^inf
                        rule_step(39, &[("a", "3"), ("b", "1"), ("c", "17"), ("d", "45"), ("e", "6")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4 01100 10^37 0 10^97 0 10^7 0^inf
                        rule_step(40, &[("a", "3"), ("b", "3"), ("c", "0"), ("d", "18"), ("e", "46"), ("f", "2")]),
                        // 0^inf 1100101 B> 10^12 01100 10^10 01100 10^3 0 10^39 0 10^99 0 10^3 0^inf
                        rule_step(41, &[("a", "5"), ("b", "3"), ("c", "1"), ("d", "17"), ("e", "1"), ("f", "2"), ("n", "24")]),
                        // 0^inf 1100101 B> 10^108 01100 10^10 01100 10^51 0 10^87 0 10^3 0 10^3 0^inf
                        rule_step(42, &[("a", "53"), ("b", "3"), ("c", "25"), ("d", "41"), ("e", "1")]),
                        // 0^inf 1100101 B> 10^112 01100 10^9 0 10^58 0 10^86 1100 10^2 0^inf
                        rule_step(15, &[("a", "54"), ("b", "0"), ("c", "4")]),
                        // 0^inf 1100101 B> 10^116 0 10^14 0 10^55 0 10^86 1100 10^2 0^inf
                        rule_step(10, &[("a", "56"), ("b", "6"), ("c", "3"), ("n", "13")]),
                        // 0^inf 1100101 B> 10^168 0 10^66 0 10^3 0 10^86 1100 10^2 0^inf
                        rule_step(43, &[("a", "82"), ("b", "32"), ("c", "42")]),
                        // 0^inf 1100101 B> 10^172 0 10^70 1100 10^85 0 10^4 0^inf
                        rule_step(15, &[("a", "84"), ("b", "35"), ("c", "42")]),
                        // 0^inf 1100101 B> 10^176 0 10^160 01 0^inf
                        rule_step(35, &[("a", "87"), ("b", "78")]),
                        // 0^inf 1100101 B> 10^8 0 10^175 01100 10^158 0^inf
                        rule_step(13, &[("a", "3"), ("b", "87"), ("c", "0"), ("d", "156")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^176 01100 10^157 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "44")]),
                        // 0^inf 1100101 B> 10^184 0 10^182 001100 10^157 0^inf
                    ]),
                },
                // 93: A(2a, b, c)  -->  B(3a+3b+34, 16a+18b+152, c)
                Rule {
                    init_config: a("2a", "b", "c"),
                    final_config: b("3a+3b+34", "16a+18b+152", "c"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^8a+4 0 10^4b+2 001100 10^c+34 0^inf
                        rule_step(14, &[("a", "4a+1"), ("b", "2b+1"), ("c", "c+31")]),
                        // 0^inf 1100101 B> 10^8a+8 01100 10^4b+5 0 10^3 0 10^c+32 0^inf
                        rule_step(15, &[("a", "4a+2"), ("b", "0"), ("c", "2b+2")]),
                        // 0^inf 1100101 B> 10^8a+12 0 10^4b+10 00 10^c+32 0^inf
                        rule_step(16, &[("a", "4a+5"), ("b", "2b+5"), ("c", "c+30")]),
                        // 0^inf 1100101 B> 10^8 0 10^8a+10 0 10^4b+10 1100 10^c+31 0^inf
                        rule_step(10, &[("a", "2"), ("b", "4a+4"), ("c", "2"), ("n", "b+2")]),
                        // 0^inf 1100101 B> 10^4b+16 0 10^8a+4b+18 0 10^2 1100 10^c+31 0^inf
                        rule_step(17, &[("a", "2b+6"), ("b", "4a+2b+8"), ("c", "c+30")]),
                        // 0^inf 1100101 B> 10^8 0 10^4b+15 0 10^8a+4b+21 0 10^c+31 0^inf
                        rule_step(18, &[("a", "3"), ("b", "2b+7"), ("c", "4a+2b+10"), ("d", "c+30")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4b+15 0 10^8a+4b+21 0 10^c+31 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "b+3")]),
                        // 0^inf 1100101 B> 10^4b+20 0 10^4b+18 0 10^3 0 10^8a+4b+21 0 10^c+31 0^inf
                        rule_step(19, &[("a", "2b+8"), ("b", "2b+8"), ("c", "4a+2b+10")]),
                        // 0^inf 1100101 B> 10^4b+24 0 10^4b+22 1100 10^8a+4b+20 0 10^c+30 0^inf
                        rule_step(20, &[("a", "2b+11"), ("b", "2b+11"), ("c", "4a+2b+9"), ("d", "c+29")]),
                        // 0^inf 1100101 B> 10^8 0 10^4b+23 01100 10^8a+8b+41 0 10^c+30 0^inf
                        rule_step(21, &[("a", "3"), ("b", "2b+9"), ("c", "4a+4b+20"), ("d", "c+26")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4b+19 0 10^8a+8b+47 0 10^c+27 0^inf
                        rule_step(39, &[("a", "3"), ("b", "1"), ("c", "2b+9"), ("d", "4a+4b+21"), ("e", "c+22")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4 01100 10^4b+21 0 10^8a+8b+49 0 10^c+23 0^inf
                        rule_step(40, &[("a", "3"), ("b", "3"), ("c", "0"), ("d", "2b+10"), ("e", "4a+4b+22"), ("f", "c+18")]),
                        // 0^inf 1100101 B> 10^12 01100 10^10 01100 10^3 0 10^4b+23 0 10^8a+8b+51 0 10^c+19 0^inf
                        rule_step(41, &[("a", "5"), ("b", "3"), ("c", "1"), ("d", "2b+9"), ("e", "1"), ("f", "c+18"), ("n", "2a+2b+12")]),
                        // 0^inf 1100101 B> 10^8a+8b+60 01100 10^10 01100 10^4a+4b+27 0 10^4a+8b+47 0 10^3 0 10^c+19 0^inf
                        rule_step(42, &[("a", "4a+4b+29"), ("b", "3"), ("c", "2a+2b+13"), ("d", "2a+4b+21"), ("e", "c+17")]),
                        // 0^inf 1100101 B> 10^8a+8b+64 01100 10^9 0 10^4a+4b+34 0 10^4a+8b+46 1100 10^c+18 0^inf
                        rule_step(15, &[("a", "4a+4b+30"), ("b", "0"), ("c", "4")]),
                        // 0^inf 1100101 B> 10^8a+8b+68 0 10^14 0 10^4a+4b+31 0 10^4a+8b+46 1100 10^c+18 0^inf
                        rule_step(10, &[("a", "4a+4b+32"), ("b", "6"), ("c", "3"), ("n", "a+b+7")]),
                        // 0^inf 1100101 B> 10^12a+12b+96 0 10^4a+4b+42 0 10^3 0 10^4a+8b+46 1100 10^c+18 0^inf
                        rule_step(44, &[("a", "6a+6b+46"), ("b", "2a+2b+20"), ("c", "2a+4b+22"), ("d", "c+15")]),
                        // 0^inf 1100101 B> 10^12a+12b+100 0 10^4a+4b+46 1100 10^4a+8b+45 0 10^4 0 10^c+16 0^inf
                        rule_step(15, &[("a", "6a+6b+48"), ("b", "2a+2b+23"), ("c", "2a+4b+22")]),
                        // 0^inf 1100101 B> 10^12a+12b+104 0 10^8a+12b+96 0100 10^c+16 0^inf
                        rule_step(45, &[("a", "6a+6b+51"), ("b", "4a+6b+47"), ("c", "c+14")]),
                        // 0^inf 1100101 B> 10^8 0 10^12a+12b+103 01100 10^8a+12b+94 1100 10^c+15 0^inf
                        rule_step(46, &[("a", "3"), ("b", "6a+6b+50"), ("c", "4a+6b+46"), ("d", "c+8")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^12a+12b+104 0 10^8a+12b+95 0 10^9 0 10^c+9 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "3a+3b+26")]),
                        // 0^inf 1100101 B> 10^12a+12b+112 0 10^12a+12b+110 00 10^8a+12b+95 0 10^9 0 10^c+9 0^inf
                        rule_step(47, &[("a", "6a+6b+54"), ("b", "6a+6b+54"), ("c", "4a+6b+47"), ("d", "3"), ("e", "c+4")]),
                        // 0^inf 1100101 B> 10^8 0 10^12a+12b+111 0 10^20a+24b+205 0 10^13 0 10^c+5 0^inf
                        rule_step(48, &[("a", "3"), ("b", "6a+6b+55"), ("c", "10a+12b+102"), ("d", "6"), ("e", "c+4")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^12a+12b+111 0 10^20a+24b+205 0 10^13 0 10^c+5 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "3a+3b+27")]),
                        // 0^inf 1100101 B> 10^12a+12b+116 0 10^12a+12b+114 0 10^3 0 10^20a+24b+205 0 10^13 0 10^c+5 0^inf
                        rule_step(19, &[("a", "6a+6b+56"), ("b", "6a+6b+56"), ("c", "10a+12b+102")]),
                        // 0^inf 1100101 B> 10^12a+12b+120 0 10^12a+12b+118 1100 10^20a+24b+204 0 10^12 0 10^c+5 0^inf
                        rule_step(49, &[("a", "6a+6b+59"), ("b", "6a+6b+59"), ("c", "10a+12b+100"), ("d", "5"), ("e", "c")]),
                        // 0^inf 1100101 B> 10^12a+12b+124 01100 10^32a+36b+321 0 10^17 0 10^c+1 0^inf
                        rule_step(15, &[("a", "6a+6b+60"), ("b", "0"), ("c", "16a+18b+160")]),
                        // 0^inf 1100101 B> 10^12a+12b+128 0 10^32a+36b+326 0 10^14 0 10^c+1 0^inf
                        rule_step(10, &[("a", "6a+6b+62"), ("b", "16a+18b+162"), ("c", "2"), ("n", "3")]),
                        // 0^inf 1100101 B> 10^12a+12b+140 0 10^32a+36b+338 0 10^2 0 10^c+1 0^inf
                    ]),
                },
                // 94: A(2a+1, b, c)  -->  A(3a+3b+28, 3a+3b+28, 8a+12b+c+80)
                Rule {
                    init_config: a("2a+1", "b", "c"),
                    final_config: a("3a+3b+28", "3a+3b+28", "8a+12b+c+80"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^8a+8 0 10^4b+2 001100 10^c+34 0^inf
                        rule_step(14, &[("a", "4a+3"), ("b", "2b+1"), ("c", "c+31")]),
                        // 0^inf 1100101 B> 10^8a+12 01100 10^4b+5 0 10^3 0 10^c+32 0^inf
                        rule_step(15, &[("a", "4a+4"), ("b", "0"), ("c", "2b+2")]),
                        // 0^inf 1100101 B> 10^8a+16 0 10^4b+10 00 10^c+32 0^inf
                        rule_step(16, &[("a", "4a+7"), ("b", "2b+5"), ("c", "c+30")]),
                        // 0^inf 1100101 B> 10^8 0 10^8a+14 0 10^4b+10 1100 10^c+31 0^inf
                        rule_step(10, &[("a", "2"), ("b", "4a+6"), ("c", "2"), ("n", "b+2")]),
                        // 0^inf 1100101 B> 10^4b+16 0 10^8a+4b+22 0 10^2 1100 10^c+31 0^inf
                        rule_step(17, &[("a", "2b+6"), ("b", "4a+2b+10"), ("c", "c+30")]),
                        // 0^inf 1100101 B> 10^8 0 10^4b+15 0 10^8a+4b+25 0 10^c+31 0^inf
                        rule_step(18, &[("a", "3"), ("b", "2b+7"), ("c", "4a+2b+12"), ("d", "c+30")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4b+15 0 10^8a+4b+25 0 10^c+31 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "b+3")]),
                        // 0^inf 1100101 B> 10^4b+20 0 10^4b+18 0 10^3 0 10^8a+4b+25 0 10^c+31 0^inf
                        rule_step(19, &[("a", "2b+8"), ("b", "2b+8"), ("c", "4a+2b+12")]),
                        // 0^inf 1100101 B> 10^4b+24 0 10^4b+22 1100 10^8a+4b+24 0 10^c+30 0^inf
                        rule_step(20, &[("a", "2b+11"), ("b", "2b+11"), ("c", "4a+2b+11"), ("d", "c+29")]),
                        // 0^inf 1100101 B> 10^8 0 10^4b+23 01100 10^8a+8b+45 0 10^c+30 0^inf
                        rule_step(21, &[("a", "3"), ("b", "2b+9"), ("c", "4a+4b+22"), ("d", "c+26")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4b+19 0 10^8a+8b+51 0 10^c+27 0^inf
                        rule_step(39, &[("a", "3"), ("b", "1"), ("c", "2b+9"), ("d", "4a+4b+23"), ("e", "c+22")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4 01100 10^4b+21 0 10^8a+8b+53 0 10^c+23 0^inf
                        rule_step(40, &[("a", "3"), ("b", "3"), ("c", "0"), ("d", "2b+10"), ("e", "4a+4b+24"), ("f", "c+18")]),
                        // 0^inf 1100101 B> 10^12 01100 10^10 01100 10^3 0 10^4b+23 0 10^8a+8b+55 0 10^c+19 0^inf
                        rule_step(41, &[("a", "5"), ("b", "3"), ("c", "1"), ("d", "2b+9"), ("e", "1"), ("f", "c+18"), ("n", "2a+2b+13")]),
                        // 0^inf 1100101 B> 10^8a+8b+64 01100 10^10 01100 10^4a+4b+29 0 10^4a+8b+49 0 10^3 0 10^c+19 0^inf
                        rule_step(42, &[("a", "4a+4b+31"), ("b", "3"), ("c", "2a+2b+14"), ("d", "2a+4b+22"), ("e", "c+17")]),
                        // 0^inf 1100101 B> 10^8a+8b+68 01100 10^9 0 10^4a+4b+36 0 10^4a+8b+48 1100 10^c+18 0^inf
                        rule_step(15, &[("a", "4a+4b+32"), ("b", "0"), ("c", "4")]),
                        // 0^inf 1100101 B> 10^8a+8b+72 0 10^14 0 10^4a+4b+33 0 10^4a+8b+48 1100 10^c+18 0^inf
                        rule_step(10, &[("a", "4a+4b+34"), ("b", "6"), ("c", "1"), ("n", "a+b+8")]),
                        // 0^inf 1100101 B> 10^12a+12b+104 0 10^4a+4b+46 0100 10^4a+8b+48 1100 10^c+18 0^inf
                        rule_step(50, &[("a", "6a+6b+50"), ("b", "2a+2b+22"), ("c", "2a+4b+23"), ("d", "c+15")]),
                        // 0^inf 1100101 B> 10^12a+12b+108 0 10^8a+12b+98 0 10^3 0 10^c+16 0^inf
                        rule_step(34, &[("a", "6a+6b+52"), ("b", "4a+6b+48"), ("c", "c+14")]),
                        // 0^inf 1100101 B> 10^8 0 10^12a+12b+107 0 10^8a+12b+100 1100 10^c+15 0^inf
                        rule_step(13, &[("a", "3"), ("b", "6a+6b+53"), ("c", "4a+6b+50"), ("d", "c+13")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^12a+12b+108 01100 10^8a+12b+c+114 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "3a+3b+27")]),
                        // 0^inf 1100101 B> 10^12a+12b+116 0 10^12a+12b+114 001100 10^8a+12b+c+114 0^inf
                    ]),
                },
                // 95: B(a, b, 0)  -->  A(a+4, a+4, 2b+1)
                Rule {
                    init_config: b("a", "b", "0"),
                    final_config: a("a+4", "a+4", "2b+1"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^4a+4 0 10^2b+34 0 10^2 01 0^inf
                        rule_step(51, &[("a", "2a+1"), ("b", "b+16")]),
                        // 0^inf 1100101 B> 10^4a+8 01100 10^2b+34 11 0^inf
                        rule_step(52, &[("a", "2a+3"), ("b", "b+17")]),
                        // 0^inf 1100101 B> 10^4a+12 01100 10^2b+37 0^inf
                        rule_step(12, &[("a", "2a+5"), ("b", "0"), ("c", "2b+35")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+11 01100 10^2b+36 0^inf
                        rule_step(13, &[("a", "3"), ("b", "2a+5"), ("c", "0"), ("d", "2b+34")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+12 01100 10^2b+35 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "a+3")]),
                        // 0^inf 1100101 B> 10^4a+20 0 10^4a+18 001100 10^2b+35 0^inf
                    ]),
                },
                // 96: B(a, b, 1)  -->  A(a+3, a+3, 2b+1)
                Rule {
                    init_config: b("a", "b", "1"),
                    final_config: a("a+3", "a+3", "2b+1"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^4a+4 0 10^2b+34 0 10^2 0 10^2 0^inf
                        rule_step(53, &[("a", "2a+1"), ("b", "b+16"), ("c", "0")]),
                        // 0^inf 1100101 B> 10^4a+8 01100 10^2b+34 11001 0^inf
                        rule_step(54, &[("a", "2a+3"), ("b", "b+16")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+7 01100 10^2b+36 0^inf
                        rule_step(13, &[("a", "3"), ("b", "2a+3"), ("c", "0"), ("d", "2b+34")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+8 01100 10^2b+35 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "a+2")]),
                        // 0^inf 1100101 B> 10^4a+16 0 10^4a+14 001100 10^2b+35 0^inf
                    ]),
                },
                // 97: B(a, b, 2)  -->  A(a+5, a+5, 2b+3)
                Rule {
                    init_config: b("a", "b", "2"),
                    final_config: a("a+5", "a+5", "2b+3"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^4a+4 0 10^2b+34 0 10^2 0 10^3 0^inf
                        rule_step(53, &[("a", "2a+1"), ("b", "b+16"), ("c", "1")]),
                        // 0^inf 1100101 B> 10^4a+8 01100 10^2b+34 1100 10^2 0^inf
                        rule_step(55, &[("a", "2a+3"), ("b", "b+16")]),
                        // 0^inf 1100101 B> 10^4a+12 01100 10^2b+35 0 10^4 0^inf
                        rule_step(15, &[("a", "2a+4"), ("b", "0"), ("c", "b+17")]),
                        // 0^inf 1100101 B> 10^4a+16 0 10^2b+40 01 0^inf
                        rule_step(35, &[("a", "2a+7"), ("b", "b+18")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+15 01100 10^2b+38 0^inf
                        rule_step(13, &[("a", "3"), ("b", "2a+7"), ("c", "0"), ("d", "2b+36")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+16 01100 10^2b+37 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "a+4")]),
                        // 0^inf 1100101 B> 10^4a+24 0 10^4a+22 001100 10^2b+37 0^inf
                    ]),
                },
                // 98: B(a, b, 3)  -->  A(a+7, a+7, 4a+2b+21)
                Rule {
                    init_config: b("a", "b", "3"),
                    final_config: a("a+7", "a+7", "4a+2b+21"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^4a+4 0 10^2b+34 0 10^2 0 10^4 0^inf
                        rule_step(53, &[("a", "2a+1"), ("b", "b+16"), ("c", "2")]),
                        // 0^inf 1100101 B> 10^4a+8 01100 10^2b+34 1100 10^3 0^inf
                        rule_step(56, &[("a", "2a+3"), ("b", "b+16")]),
                        // 0^inf 1100101 B> 10^4a+12 01100 10^2b+36 01100 10^2 0^inf
                        rule_step(57, &[("a", "2a+5"), ("b", "b+17"), ("c", "0")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+11 01100 10^2b+36 011001 0^inf
                        rule_step(58, &[("a", "3"), ("b", "2a+5"), ("c", "b+17")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+12 01100 10^2b+36 011 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "a+3")]),
                        // 0^inf 1100101 B> 10^4a+20 0 10^4a+18 001100 10^2b+36 011 0^inf
                        rule_step(59, &[("a", "2a+9"), ("b", "2a+8"), ("c", "b+17")]),
                        // 0^inf 1100101 B> 10^4a+24 01100 10^4a+2b+57 0^inf
                        rule_step(12, &[("a", "2a+11"), ("b", "0"), ("c", "4a+2b+55")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+23 01100 10^4a+2b+56 0^inf
                        rule_step(13, &[("a", "3"), ("b", "2a+11"), ("c", "0"), ("d", "4a+2b+54")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+24 01100 10^4a+2b+55 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "a+6")]),
                        // 0^inf 1100101 B> 10^4a+32 0 10^4a+30 001100 10^4a+2b+55 0^inf
                    ]),
                },
                // 99: B(a, 2b, 4)  -->  A(a+2b+35, a+2b+35, 8a+12b+170)
                Rule {
                    init_config: b("a", "2b", "4"),
                    final_config: a("a+2b+35", "a+2b+35", "8a+12b+170"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^4a+4 0 10^4b+34 0 10^2 0 10^5 0^inf
                        rule_step(53, &[("a", "2a+1"), ("b", "2b+16"), ("c", "3")]),
                        // 0^inf 1100101 B> 10^4a+8 01100 10^4b+34 1100 10^4 0^inf
                        rule_step(60, &[("a", "2a+2"), ("b", "2b+16")]),
                        // 0^inf 1100101 B> 10^4a+12 0 10^4b+41 0 10^4 0^inf
                        rule_step(33, &[("a", "2a+5"), ("b", "2b+20"), ("c", "3")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+10 0 10^4b+41 0 10^4 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2a+4"), ("c", "1"), ("n", "b+10")]),
                        // 0^inf 1100101 B> 10^4b+48 0 10^4a+4b+50 0100 10^4 0^inf
                        rule_step(45, &[("a", "2b+23"), ("b", "2a+2b+24"), ("c", "2")]),
                        // 0^inf 1100101 B> 10^8 0 10^4b+47 01100 10^4a+4b+48 1100 10^3 0^inf
                        rule_step(61, &[("a", "3"), ("b", "2b+23"), ("c", "2a+2b+23")]),
                        // 0^inf 1100101 B> 10^12 01100 10^4b+50 01100 10^4a+4b+49 0 10^2 0^inf
                        rule_step(62, &[("a", "5"), ("b", "2b+23"), ("c", "2a+2b+24")]),
                        // 0^inf 1100101 B> 10^8 0 10^11 01100 10^4b+50 0 10^4a+4b+52 0^inf
                        rule_step(63, &[("a", "3"), ("b", "5"), ("c", "2b+24"), ("d", "4a+4b+51")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^12 01100 10^4b+49 0 10^4a+4b+52 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "3")]),
                        // 0^inf 1100101 B> 10^20 0 10^18 001100 10^4b+49 0 10^4a+4b+52 0^inf
                        rule_step(64, &[("a", "9"), ("b", "9"), ("c", "2b+23"), ("d", "4a+4b+51")]),
                        // 0^inf 1100101 B> 10^24 01100 10^21 0 10^3 0 10^4b+47 0 10^4a+4b+52 0^inf
                        rule_step(15, &[("a", "10"), ("b", "0"), ("c", "10")]),
                        // 0^inf 1100101 B> 10^28 0 10^26 00 10^4b+47 0 10^4a+4b+52 0^inf
                        rule_step(65, &[("a", "13"), ("b", "12"), ("c", "2b+23"), ("d", "4a+4b+50")]),
                        // 0^inf 1100101 B> 10^32 01100 10^4b+73 0 10^4a+4b+51 0^inf
                        rule_step(15, &[("a", "14"), ("b", "0"), ("c", "2b+36")]),
                        // 0^inf 1100101 B> 10^36 0 10^4b+78 0 10^4a+4b+48 0^inf
                        rule_step(10, &[("a", "16"), ("b", "2b+38"), ("c", "0"), ("n", "a+b+12")]),
                        // 0^inf 1100101 B> 10^4a+4b+84 0 10^4a+8b+126 0^inf
                        rule_step(9, &[("a", "2a+2b+41"), ("b", "4a+8b+125")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+4b+82 0 10^4a+8b+126 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2a+2b+40"), ("c", "2"), ("n", "a+2b+31")]),
                        // 0^inf 1100101 B> 10^4a+8b+132 0 10^8a+12b+206 0 10^2 0^inf
                        rule_step(11, &[("a", "2a+4b+65"), ("b", "4a+6b+102")]),
                        // 0^inf 1100101 B> 10^4a+8b+136 01100 10^8a+12b+206 0^inf
                        rule_step(12, &[("a", "2a+4b+67"), ("b", "0"), ("c", "8a+12b+204")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+8b+135 01100 10^8a+12b+205 0^inf
                        rule_step(13, &[("a", "3"), ("b", "2a+4b+67"), ("c", "0"), ("d", "8a+12b+203")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+8b+136 01100 10^8a+12b+204 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "a+2b+34")]),
                        // 0^inf 1100101 B> 10^4a+8b+144 0 10^4a+8b+142 001100 10^8a+12b+204 0^inf
                    ]),
                },
                // 100: B(a, 2b+1, 4)  -->  A(b+13, b+13, 4a+4b+20)
                Rule {
                    init_config: b("a", "2b+1", "4"),
                    final_config: a("b+13", "b+13", "4a+4b+20"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^4a+4 0 10^4b+36 0 10^2 0 10^5 0^inf
                        rule_step(53, &[("a", "2a+1"), ("b", "2b+17"), ("c", "3")]),
                        // 0^inf 1100101 B> 10^4a+8 01100 10^4b+36 1100 10^4 0^inf
                        rule_step(60, &[("a", "2a+2"), ("b", "2b+17")]),
                        // 0^inf 1100101 B> 10^4a+12 0 10^4b+43 0 10^4 0^inf
                        rule_step(33, &[("a", "2a+5"), ("b", "2b+21"), ("c", "3")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+10 0 10^4b+43 0 10^4 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2a+4"), ("c", "3"), ("n", "b+10")]),
                        // 0^inf 1100101 B> 10^4b+48 0 10^4a+4b+50 0 10^3 0 10^4 0^inf
                        rule_step(34, &[("a", "2b+22"), ("b", "2a+2b+24"), ("c", "2")]),
                        // 0^inf 1100101 B> 10^8 0 10^4b+47 0 10^4a+4b+52 1100 10^3 0^inf
                        rule_step(13, &[("a", "3"), ("b", "2b+23"), ("c", "2a+2b+26"), ("d", "1")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4b+48 01100 10^4a+4b+54 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "b+12")]),
                        // 0^inf 1100101 B> 10^4b+56 0 10^4b+54 001100 10^4a+4b+54 0^inf
                    ]),
                },
                // 101: B(2a, b, 5)  -->  A(3a+46, 3a+46, 20a+2b+340)
                Rule {
                    init_config: b("2a", "b", "5"),
                    final_config: a("3a+46", "3a+46", "20a+2b+340"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^8a+4 0 10^2b+34 0 10^2 0 10^6 0^inf
                        rule_step(53, &[("a", "4a+1"), ("b", "b+16"), ("c", "4")]),
                        // 0^inf 1100101 B> 10^8a+8 01100 10^2b+34 1100 10^5 0^inf
                        rule_step(66, &[("a", "4a+3"), ("b", "b+16")]),
                        // 0^inf 1100101 B> 10^8a+12 01100 10^2b+36 0 10^6 0^inf
                        rule_step(20, &[("a", "4a+5"), ("b", "0"), ("c", "b+17"), ("d", "5")]),
                        // 0^inf 1100101 B> 10^8 0 10^8a+11 01100 10^2b+35 0 10^6 0^inf
                        rule_step(21, &[("a", "3"), ("b", "4a+3"), ("c", "b+17"), ("d", "2")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^8a+7 0 10^2b+41 0 10^3 0^inf
                        rule_step(67, &[("a", "3"), ("b", "1"), ("c", "4a+3"), ("d", "b+18")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^3 0 10^8a+14 0 10^2b+40 0^inf
                        rule_step(68, &[("a", "3"), ("b", "1"), ("c", "1"), ("d", "4a+5"), ("e", "2b+39")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^3 0 10^9 0 10^8a+11 0 10^2b+40 0^inf
                        rule_step(69, &[("a", "3"), ("b", "1"), ("c", "1"), ("d", "2"), ("e", "4a+3"), ("f", "2b+39")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4 01100 10^5 0 10^11 0 10^8a+7 0 10^2b+40 0^inf
                        rule_step(70, &[("a", "3"), ("b", "3"), ("c", "0"), ("d", "2"), ("e", "3"), ("f", "4a+1"), ("g", "2b+39")]),
                        // 0^inf 1100101 B> 10^12 01100 10^10 01100 10^3 0 10^7 0 10^13 0 10^8a+3 0 10^2b+40 0^inf
                        rule_step(71, &[("a", "5"), ("b", "3"), ("c", "1"), ("d", "1"), ("e", "0"), ("f", "4a+1"), ("g", "2b+39"), ("n", "3")]),
                        // 0^inf 1100101 B> 10^24 01100 10^10 01100 10^9 0 10^13 0100 10^8a+3 0 10^2b+40 0^inf
                        rule_step(72, &[("a", "11"), ("b", "3"), ("c", "4"), ("d", "4"), ("e", "4a+1"), ("f", "2b+38")]),
                        // 0^inf 1100101 B> 10^28 01100 10^9 0 10^16 0 10^8a+15 0 10^2b+39 0^inf
                        rule_step(15, &[("a", "12"), ("b", "0"), ("c", "4")]),
                        // 0^inf 1100101 B> 10^32 0 10^14 0 10^13 0 10^8a+15 0 10^2b+39 0^inf
                        rule_step(10, &[("a", "14"), ("b", "6"), ("c", "1"), ("n", "3")]),
                        // 0^inf 1100101 B> 10^44 0 10^26 0100 10^8a+15 0 10^2b+39 0^inf
                        rule_step(73, &[("a", "20"), ("b", "12"), ("c", "4a+7"), ("d", "2b+37")]),
                        // 0^inf 1100101 B> 10^8 0 10^43 0 10^8a+43 0 10^2b+38 0^inf
                        rule_step(18, &[("a", "3"), ("b", "21"), ("c", "4a+21"), ("d", "2b+37")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^43 0 10^8a+43 0 10^2b+38 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "10")]),
                        // 0^inf 1100101 B> 10^48 0 10^46 0 10^3 0 10^8a+43 0 10^2b+38 0^inf
                        rule_step(19, &[("a", "22"), ("b", "22"), ("c", "4a+21")]),
                        // 0^inf 1100101 B> 10^52 0 10^50 1100 10^8a+42 0 10^2b+37 0^inf
                        rule_step(20, &[("a", "25"), ("b", "25"), ("c", "4a+20"), ("d", "2b+36")]),
                        // 0^inf 1100101 B> 10^8 0 10^51 01100 10^8a+91 0 10^2b+37 0^inf
                        rule_step(21, &[("a", "3"), ("b", "23"), ("c", "4a+45"), ("d", "2b+33")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^47 0 10^8a+97 0 10^2b+34 0^inf
                        rule_step(39, &[("a", "3"), ("b", "1"), ("c", "23"), ("d", "4a+46"), ("e", "2b+29")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4 01100 10^49 0 10^8a+99 0 10^2b+30 0^inf
                        rule_step(40, &[("a", "3"), ("b", "3"), ("c", "0"), ("d", "24"), ("e", "4a+47"), ("f", "2b+25")]),
                        // 0^inf 1100101 B> 10^12 01100 10^10 01100 10^3 0 10^51 0 10^8a+101 0 10^2b+26 0^inf
                        rule_step(41, &[("a", "5"), ("b", "3"), ("c", "1"), ("d", "23"), ("e", "0"), ("f", "2b+25"), ("n", "2a+25")]),
                        // 0^inf 1100101 B> 10^8a+112 01100 10^10 01100 10^4a+53 0 10^4a+101 0100 10^2b+26 0^inf
                        rule_step(74, &[("a", "4a+55"), ("b", "3"), ("c", "2a+26"), ("d", "2a+48"), ("e", "2b+24")]),
                        // 0^inf 1100101 B> 10^8a+116 01100 10^9 0 10^4a+60 01100 10^4a+96 1100 10^2b+25 0^inf
                        rule_step(15, &[("a", "4a+56"), ("b", "0"), ("c", "4")]),
                        // 0^inf 1100101 B> 10^8a+120 0 10^14 0 10^4a+57 01100 10^4a+96 1100 10^2b+25 0^inf
                        rule_step(10, &[("a", "4a+58"), ("b", "6"), ("c", "1"), ("n", "a+14")]),
                        // 0^inf 1100101 B> 10^12a+176 0 10^4a+70 01001100 10^4a+96 1100 10^2b+25 0^inf
                        rule_step(75, &[("a", "6a+86"), ("b", "2a+34"), ("c", "2a+47"), ("d", "2b+25")]),
                        // 0^inf 1100101 B> 10^8 0 10^12a+175 0 10^8a+2b+196 0^inf
                        rule_step(33, &[("a", "3"), ("b", "6a+87"), ("c", "8a+2b+195")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^12a+175 0 10^8a+2b+196 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "3a+43")]),
                        // 0^inf 1100101 B> 10^12a+180 0 10^12a+178 0 10^3 0 10^8a+2b+196 0^inf
                        rule_step(34, &[("a", "6a+88"), ("b", "6a+88"), ("c", "8a+2b+194")]),
                        // 0^inf 1100101 B> 10^8 0 10^12a+179 0 10^12a+180 1100 10^8a+2b+195 0^inf
                        rule_step(13, &[("a", "3"), ("b", "6a+89"), ("c", "6a+90"), ("d", "8a+2b+193")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^12a+180 01100 10^20a+2b+374 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "3a+45")]),
                        // 0^inf 1100101 B> 10^12a+188 0 10^12a+186 001100 10^20a+2b+374 0^inf
                    ]),
                },
                // 102: B(2a+1, b, 5)  -->  A(3a+47, 3a+47, 8a+2b+163)
                Rule {
                    init_config: b("2a+1", "b", "5"),
                    final_config: a("3a+47", "3a+47", "8a+2b+163"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^8a+8 0 10^2b+34 0 10^2 0 10^6 0^inf
                        rule_step(53, &[("a", "4a+3"), ("b", "b+16"), ("c", "4")]),
                        // 0^inf 1100101 B> 10^8a+12 01100 10^2b+34 1100 10^5 0^inf
                        rule_step(66, &[("a", "4a+5"), ("b", "b+16")]),
                        // 0^inf 1100101 B> 10^8a+16 01100 10^2b+36 0 10^6 0^inf
                        rule_step(20, &[("a", "4a+7"), ("b", "0"), ("c", "b+17"), ("d", "5")]),
                        // 0^inf 1100101 B> 10^8 0 10^8a+15 01100 10^2b+35 0 10^6 0^inf
                        rule_step(21, &[("a", "3"), ("b", "4a+5"), ("c", "b+17"), ("d", "2")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^8a+11 0 10^2b+41 0 10^3 0^inf
                        rule_step(67, &[("a", "3"), ("b", "1"), ("c", "4a+5"), ("d", "b+18")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^3 0 10^8a+18 0 10^2b+40 0^inf
                        rule_step(68, &[("a", "3"), ("b", "1"), ("c", "1"), ("d", "4a+7"), ("e", "2b+39")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^3 0 10^9 0 10^8a+15 0 10^2b+40 0^inf
                        rule_step(69, &[("a", "3"), ("b", "1"), ("c", "1"), ("d", "2"), ("e", "4a+5"), ("f", "2b+39")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4 01100 10^5 0 10^11 0 10^8a+11 0 10^2b+40 0^inf
                        rule_step(70, &[("a", "3"), ("b", "3"), ("c", "0"), ("d", "2"), ("e", "3"), ("f", "4a+3"), ("g", "2b+39")]),
                        // 0^inf 1100101 B> 10^12 01100 10^10 01100 10^3 0 10^7 0 10^13 0 10^8a+7 0 10^2b+40 0^inf
                        rule_step(71, &[("a", "5"), ("b", "3"), ("c", "1"), ("d", "1"), ("e", "0"), ("f", "4a+3"), ("g", "2b+39"), ("n", "3")]),
                        // 0^inf 1100101 B> 10^24 01100 10^10 01100 10^9 0 10^13 0100 10^8a+7 0 10^2b+40 0^inf
                        rule_step(72, &[("a", "11"), ("b", "3"), ("c", "4"), ("d", "4"), ("e", "4a+3"), ("f", "2b+38")]),
                        // 0^inf 1100101 B> 10^28 01100 10^9 0 10^16 0 10^8a+19 0 10^2b+39 0^inf
                        rule_step(15, &[("a", "12"), ("b", "0"), ("c", "4")]),
                        // 0^inf 1100101 B> 10^32 0 10^14 0 10^13 0 10^8a+19 0 10^2b+39 0^inf
                        rule_step(10, &[("a", "14"), ("b", "6"), ("c", "1"), ("n", "3")]),
                        // 0^inf 1100101 B> 10^44 0 10^26 0100 10^8a+19 0 10^2b+39 0^inf
                        rule_step(73, &[("a", "20"), ("b", "12"), ("c", "4a+9"), ("d", "2b+37")]),
                        // 0^inf 1100101 B> 10^8 0 10^43 0 10^8a+47 0 10^2b+38 0^inf
                        rule_step(18, &[("a", "3"), ("b", "21"), ("c", "4a+23"), ("d", "2b+37")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^43 0 10^8a+47 0 10^2b+38 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "10")]),
                        // 0^inf 1100101 B> 10^48 0 10^46 0 10^3 0 10^8a+47 0 10^2b+38 0^inf
                        rule_step(19, &[("a", "22"), ("b", "22"), ("c", "4a+23")]),
                        // 0^inf 1100101 B> 10^52 0 10^50 1100 10^8a+46 0 10^2b+37 0^inf
                        rule_step(20, &[("a", "25"), ("b", "25"), ("c", "4a+22"), ("d", "2b+36")]),
                        // 0^inf 1100101 B> 10^8 0 10^51 01100 10^8a+95 0 10^2b+37 0^inf
                        rule_step(21, &[("a", "3"), ("b", "23"), ("c", "4a+47"), ("d", "2b+33")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^47 0 10^8a+101 0 10^2b+34 0^inf
                        rule_step(39, &[("a", "3"), ("b", "1"), ("c", "23"), ("d", "4a+48"), ("e", "2b+29")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4 01100 10^49 0 10^8a+103 0 10^2b+30 0^inf
                        rule_step(40, &[("a", "3"), ("b", "3"), ("c", "0"), ("d", "24"), ("e", "4a+49"), ("f", "2b+25")]),
                        // 0^inf 1100101 B> 10^12 01100 10^10 01100 10^3 0 10^51 0 10^8a+105 0 10^2b+26 0^inf
                        rule_step(41, &[("a", "5"), ("b", "3"), ("c", "1"), ("d", "23"), ("e", "0"), ("f", "2b+25"), ("n", "2a+26")]),
                        // 0^inf 1100101 B> 10^8a+116 01100 10^10 01100 10^4a+55 0 10^4a+103 0100 10^2b+26 0^inf
                        rule_step(74, &[("a", "4a+57"), ("b", "3"), ("c", "2a+27"), ("d", "2a+49"), ("e", "2b+24")]),
                        // 0^inf 1100101 B> 10^8a+120 01100 10^9 0 10^4a+62 01100 10^4a+98 1100 10^2b+25 0^inf
                        rule_step(15, &[("a", "4a+58"), ("b", "0"), ("c", "4")]),
                        // 0^inf 1100101 B> 10^8a+124 0 10^14 0 10^4a+59 01100 10^4a+98 1100 10^2b+25 0^inf
                        rule_step(10, &[("a", "4a+60"), ("b", "6"), ("c", "3"), ("n", "a+14")]),
                        // 0^inf 1100101 B> 10^12a+180 0 10^4a+70 0 10^3 01100 10^4a+98 1100 10^2b+25 0^inf
                        rule_step(76, &[("a", "6a+88"), ("b", "2a+34"), ("c", "2a+48"), ("d", "2b+25")]),
                        // 0^inf 1100101 B> 10^12a+184 0 10^4a+74 1100 10^4a+2b+125 0^inf
                        rule_step(12, &[("a", "6a+91"), ("b", "2a+37"), ("c", "4a+2b+123")]),
                        // 0^inf 1100101 B> 10^8 0 10^12a+183 01100 10^8a+2b+198 0^inf
                        rule_step(13, &[("a", "3"), ("b", "6a+91"), ("c", "0"), ("d", "8a+2b+196")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^12a+184 01100 10^8a+2b+197 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "3a+46")]),
                        // 0^inf 1100101 B> 10^12a+192 0 10^12a+190 001100 10^8a+2b+197 0^inf
                    ]),
                },
                // 103: B(a, 2b, 6)  -->  A(a+b+24, a+b+24, 8a+4b+74)
                Rule {
                    init_config: b("a", "2b", "6"),
                    final_config: a("a+b+24", "a+b+24", "8a+4b+74"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^4a+4 0 10^4b+34 0 10^2 0 10^7 0^inf
                        rule_step(53, &[("a", "2a+1"), ("b", "2b+16"), ("c", "5")]),
                        // 0^inf 1100101 B> 10^4a+8 01100 10^4b+34 1100 10^6 0^inf
                        rule_step(77, &[("a", "2a+2"), ("b", "2b+16")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+7 0 10^4b+35 0 10^9 0^inf
                        rule_step(18, &[("a", "3"), ("b", "2a+3"), ("c", "2b+17"), ("d", "8")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+7 0 10^4b+35 0 10^9 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "a+1")]),
                        // 0^inf 1100101 B> 10^4a+12 0 10^4a+10 0 10^3 0 10^4b+35 0 10^9 0^inf
                        rule_step(19, &[("a", "2a+4"), ("b", "2a+4"), ("c", "2b+17")]),
                        // 0^inf 1100101 B> 10^4a+16 0 10^4a+14 1100 10^4b+34 0 10^8 0^inf
                        rule_step(20, &[("a", "2a+7"), ("b", "2a+7"), ("c", "2b+16"), ("d", "7")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+15 01100 10^4a+4b+47 0 10^8 0^inf
                        rule_step(21, &[("a", "3"), ("b", "2a+5"), ("c", "2a+2b+23"), ("d", "4")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4a+11 0 10^4a+4b+53 0 10^5 0^inf
                        rule_step(39, &[("a", "3"), ("b", "1"), ("c", "2a+5"), ("d", "2a+2b+24"), ("e", "0")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4 01100 10^4a+13 0 10^4a+4b+55 01 0^inf
                        rule_step(78, &[("a", "3"), ("b", "3"), ("c", "0"), ("d", "2a+6"), ("e", "2a+2b+24")]),
                        // 0^inf 1100101 B> 10^12 01100 10^9 0 10^4 01100 10^4a+19 0 10^4a+4b+50 0^inf
                        rule_step(15, &[("a", "4"), ("b", "0"), ("c", "4")]),
                        // 0^inf 1100101 B> 10^16 0 10^14 01001100 10^4a+19 0 10^4a+4b+50 0^inf
                        rule_step(79, &[("a", "6"), ("b", "6"), ("c", "2a+8"), ("d", "4a+4b+49")]),
                        // 0^inf 1100101 B> 10^8 0 10^15 0 10^19 0 10^3 0 10^4a+17 0 10^4a+4b+50 0^inf
                        rule_step(30, &[("a", "3"), ("b", "7"), ("c", "9"), ("d", "1"), ("e", "2a+8"), ("f", "4a+4b+49")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^15 0 10^19 0 10^3 0 10^4a+17 0 10^4a+4b+50 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "3")]),
                        // 0^inf 1100101 B> 10^20 0 10^18 0 10^3 0 10^19 0 10^3 0 10^4a+17 0 10^4a+4b+50 0^inf
                        rule_step(19, &[("a", "8"), ("b", "8"), ("c", "9")]),
                        // 0^inf 1100101 B> 10^24 0 10^22 1100 10^18 0 10^2 0 10^4a+17 0 10^4a+4b+50 0^inf
                        rule_step(80, &[("a", "11"), ("b", "11"), ("c", "7"), ("d", "2a+6"), ("e", "4a+4b+49")]),
                        // 0^inf 1100101 B> 10^28 01100 10^39 0 10^7 0 10^4a+13 0 10^4a+4b+50 0^inf
                        rule_step(15, &[("a", "12"), ("b", "0"), ("c", "19")]),
                        // 0^inf 1100101 B> 10^32 0 10^44 0 10^4 0 10^4a+13 0 10^4a+4b+50 0^inf
                        rule_step(10, &[("a", "14"), ("b", "21"), ("c", "0"), ("n", "1")]),
                        // 0^inf 1100101 B> 10^36 0 10^48 00 10^4a+13 0 10^4a+4b+50 0^inf
                        rule_step(65, &[("a", "17"), ("b", "23"), ("c", "2a+6"), ("d", "4a+4b+48")]),
                        // 0^inf 1100101 B> 10^40 01100 10^4a+61 0 10^4a+4b+49 0^inf
                        rule_step(15, &[("a", "18"), ("b", "0"), ("c", "2a+30")]),
                        // 0^inf 1100101 B> 10^44 0 10^4a+66 0 10^4a+4b+46 0^inf
                        rule_step(10, &[("a", "20"), ("b", "2a+32"), ("c", "2"), ("n", "a+b+11")]),
                        // 0^inf 1100101 B> 10^4a+4b+88 0 10^8a+4b+110 0 10^2 0^inf
                        rule_step(11, &[("a", "2a+2b+43"), ("b", "4a+2b+54")]),
                        // 0^inf 1100101 B> 10^4a+4b+92 01100 10^8a+4b+110 0^inf
                        rule_step(12, &[("a", "2a+2b+45"), ("b", "0"), ("c", "8a+4b+108")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+4b+91 01100 10^8a+4b+109 0^inf
                        rule_step(13, &[("a", "3"), ("b", "2a+2b+45"), ("c", "0"), ("d", "8a+4b+107")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+4b+92 01100 10^8a+4b+108 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "a+b+23")]),
                        // 0^inf 1100101 B> 10^4a+4b+100 0 10^4a+4b+98 001100 10^8a+4b+108 0^inf
                    ]),
                },
                // 104: B(a, 2b+1, 6)  -->  A(2a+b+32, 2a+b+32, 12a+8b+166)
                Rule {
                    init_config: b("a", "2b+1", "6"),
                    final_config: a("2a+b+32", "2a+b+32", "12a+8b+166"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^4a+4 0 10^4b+36 0 10^2 0 10^7 0^inf
                        rule_step(53, &[("a", "2a+1"), ("b", "2b+17"), ("c", "5")]),
                        // 0^inf 1100101 B> 10^4a+8 01100 10^4b+36 1100 10^6 0^inf
                        rule_step(77, &[("a", "2a+2"), ("b", "2b+17")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+7 0 10^4b+37 0 10^9 0^inf
                        rule_step(18, &[("a", "3"), ("b", "2a+3"), ("c", "2b+18"), ("d", "8")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+7 0 10^4b+37 0 10^9 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "a+1")]),
                        // 0^inf 1100101 B> 10^4a+12 0 10^4a+10 0 10^3 0 10^4b+37 0 10^9 0^inf
                        rule_step(19, &[("a", "2a+4"), ("b", "2a+4"), ("c", "2b+18")]),
                        // 0^inf 1100101 B> 10^4a+16 0 10^4a+14 1100 10^4b+36 0 10^8 0^inf
                        rule_step(20, &[("a", "2a+7"), ("b", "2a+7"), ("c", "2b+17"), ("d", "7")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+15 01100 10^4a+4b+49 0 10^8 0^inf
                        rule_step(21, &[("a", "3"), ("b", "2a+5"), ("c", "2a+2b+24"), ("d", "4")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4a+11 0 10^4a+4b+55 0 10^5 0^inf
                        rule_step(39, &[("a", "3"), ("b", "1"), ("c", "2a+5"), ("d", "2a+2b+25"), ("e", "0")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4 01100 10^4a+13 0 10^4a+4b+57 01 0^inf
                        rule_step(78, &[("a", "3"), ("b", "3"), ("c", "0"), ("d", "2a+6"), ("e", "2a+2b+25")]),
                        // 0^inf 1100101 B> 10^12 01100 10^9 0 10^4 01100 10^4a+19 0 10^4a+4b+52 0^inf
                        rule_step(15, &[("a", "4"), ("b", "0"), ("c", "4")]),
                        // 0^inf 1100101 B> 10^16 0 10^14 01001100 10^4a+19 0 10^4a+4b+52 0^inf
                        rule_step(79, &[("a", "6"), ("b", "6"), ("c", "2a+8"), ("d", "4a+4b+51")]),
                        // 0^inf 1100101 B> 10^8 0 10^15 0 10^19 0 10^3 0 10^4a+17 0 10^4a+4b+52 0^inf
                        rule_step(30, &[("a", "3"), ("b", "7"), ("c", "9"), ("d", "1"), ("e", "2a+8"), ("f", "4a+4b+51")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^15 0 10^19 0 10^3 0 10^4a+17 0 10^4a+4b+52 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "3")]),
                        // 0^inf 1100101 B> 10^20 0 10^18 0 10^3 0 10^19 0 10^3 0 10^4a+17 0 10^4a+4b+52 0^inf
                        rule_step(19, &[("a", "8"), ("b", "8"), ("c", "9")]),
                        // 0^inf 1100101 B> 10^24 0 10^22 1100 10^18 0 10^2 0 10^4a+17 0 10^4a+4b+52 0^inf
                        rule_step(80, &[("a", "11"), ("b", "11"), ("c", "7"), ("d", "2a+6"), ("e", "4a+4b+51")]),
                        // 0^inf 1100101 B> 10^28 01100 10^39 0 10^7 0 10^4a+13 0 10^4a+4b+52 0^inf
                        rule_step(15, &[("a", "12"), ("b", "0"), ("c", "19")]),
                        // 0^inf 1100101 B> 10^32 0 10^44 0 10^4 0 10^4a+13 0 10^4a+4b+52 0^inf
                        rule_step(10, &[("a", "14"), ("b", "21"), ("c", "0"), ("n", "1")]),
                        // 0^inf 1100101 B> 10^36 0 10^48 00 10^4a+13 0 10^4a+4b+52 0^inf
                        rule_step(65, &[("a", "17"), ("b", "23"), ("c", "2a+6"), ("d", "4a+4b+50")]),
                        // 0^inf 1100101 B> 10^40 01100 10^4a+61 0 10^4a+4b+51 0^inf
                        rule_step(15, &[("a", "18"), ("b", "0"), ("c", "2a+30")]),
                        // 0^inf 1100101 B> 10^44 0 10^4a+66 0 10^4a+4b+48 0^inf
                        rule_step(10, &[("a", "20"), ("b", "2a+32"), ("c", "0"), ("n", "a+b+12")]),
                        // 0^inf 1100101 B> 10^4a+4b+92 0 10^8a+4b+114 0^inf
                        rule_step(9, &[("a", "2a+2b+45"), ("b", "8a+4b+113")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+4b+90 0 10^8a+4b+114 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2a+2b+44"), ("c", "2"), ("n", "2a+b+28")]),
                        // 0^inf 1100101 B> 10^8a+4b+120 0 10^12a+8b+202 0 10^2 0^inf
                        rule_step(11, &[("a", "4a+2b+59"), ("b", "6a+4b+100")]),
                        // 0^inf 1100101 B> 10^8a+4b+124 01100 10^12a+8b+202 0^inf
                        rule_step(12, &[("a", "4a+2b+61"), ("b", "0"), ("c", "12a+8b+200")]),
                        // 0^inf 1100101 B> 10^8 0 10^8a+4b+123 01100 10^12a+8b+201 0^inf
                        rule_step(13, &[("a", "3"), ("b", "4a+2b+61"), ("c", "0"), ("d", "12a+8b+199")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^8a+4b+124 01100 10^12a+8b+200 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "2a+b+31")]),
                        // 0^inf 1100101 B> 10^8a+4b+132 0 10^8a+4b+130 001100 10^12a+8b+200 0^inf
                    ]),
                },
                // 105: B(a, b, 7)  -->  A(a+10, a+10, 8a+2b+42)
                Rule {
                    init_config: b("a", "b", "7"),
                    final_config: a("a+10", "a+10", "8a+2b+42"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^4a+4 0 10^2b+34 0 10^2 0 10^8 0^inf
                        rule_step(53, &[("a", "2a+1"), ("b", "b+16"), ("c", "6")]),
                        // 0^inf 1100101 B> 10^4a+8 01100 10^2b+34 1100 10^7 0^inf
                        rule_step(81, &[("a", "2a+2"), ("b", "b+16"), ("c", "0")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+7 0 10^2b+35 0 10^9 01 0^inf
                        rule_step(48, &[("a", "3"), ("b", "2a+3"), ("c", "b+17"), ("d", "4"), ("e", "0")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+7 0 10^2b+35 0 10^9 01 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "a+1")]),
                        // 0^inf 1100101 B> 10^4a+12 0 10^4a+10 0 10^3 0 10^2b+35 0 10^9 01 0^inf
                        rule_step(19, &[("a", "2a+4"), ("b", "2a+4"), ("c", "b+17")]),
                        // 0^inf 1100101 B> 10^4a+16 0 10^4a+14 1100 10^2b+34 0 10^8 01 0^inf
                        rule_step(82, &[("a", "2a+7"), ("b", "2a+7"), ("c", "b+16"), ("d", "2")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+15 01100 10^4a+2b+48 01100 10^6 0^inf
                        rule_step(83, &[("a", "3"), ("b", "2a+7"), ("c", "2a+b+23"), ("d", "4")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+16 01100 10^4a+2b+48 01100 10^5 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "a+4")]),
                        // 0^inf 1100101 B> 10^4a+24 0 10^4a+22 001100 10^4a+2b+48 01100 10^5 0^inf
                        rule_step(84, &[("a", "2a+11"), ("b", "2a+10"), ("c", "2a+b+23"), ("d", "4")]),
                        // 0^inf 1100101 B> 10^4a+28 01100 10^8a+2b+73 0 10^5 0^inf
                        rule_step(15, &[("a", "2a+12"), ("b", "0"), ("c", "4a+b+36")]),
                        // 0^inf 1100101 B> 10^4a+32 0 10^8a+2b+78 0 10^2 0^inf
                        rule_step(11, &[("a", "2a+15"), ("b", "4a+b+38")]),
                        // 0^inf 1100101 B> 10^4a+36 01100 10^8a+2b+78 0^inf
                        rule_step(12, &[("a", "2a+17"), ("b", "0"), ("c", "8a+2b+76")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+35 01100 10^8a+2b+77 0^inf
                        rule_step(13, &[("a", "3"), ("b", "2a+17"), ("c", "0"), ("d", "8a+2b+75")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+36 01100 10^8a+2b+76 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "a+9")]),
                        // 0^inf 1100101 B> 10^4a+44 0 10^4a+42 001100 10^8a+2b+76 0^inf
                    ]),
                },
                // 106: B(a, 2b, 8)  -->  A(2a+b+26, 2a+b+26, 12a+4b+82)
                Rule {
                    init_config: b("a", "2b", "8"),
                    final_config: a("2a+b+26", "2a+b+26", "12a+4b+82"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^4a+4 0 10^4b+34 0 10^2 0 10^9 0^inf
                        rule_step(53, &[("a", "2a+1"), ("b", "2b+16"), ("c", "7")]),
                        // 0^inf 1100101 B> 10^4a+8 01100 10^4b+34 1100 10^8 0^inf
                        rule_step(81, &[("a", "2a+2"), ("b", "2b+16"), ("c", "1")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+7 0 10^4b+35 0 10^9 0 10^2 0^inf
                        rule_step(48, &[("a", "3"), ("b", "2a+3"), ("c", "2b+17"), ("d", "4"), ("e", "1")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+7 0 10^4b+35 0 10^9 0 10^2 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "a+1")]),
                        // 0^inf 1100101 B> 10^4a+12 0 10^4a+10 0 10^3 0 10^4b+35 0 10^9 0 10^2 0^inf
                        rule_step(19, &[("a", "2a+4"), ("b", "2a+4"), ("c", "2b+17")]),
                        // 0^inf 1100101 B> 10^4a+16 0 10^4a+14 1100 10^4b+34 0 10^8 0 10^2 0^inf
                        rule_step(85, &[("a", "2a+6"), ("b", "2a+7"), ("c", "2b+16"), ("d", "3")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+15 0 10^4a+4b+53 0 10^8 0^inf
                        rule_step(18, &[("a", "3"), ("b", "2a+7"), ("c", "2a+2b+26"), ("d", "7")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+15 0 10^4a+4b+53 0 10^8 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "a+3")]),
                        // 0^inf 1100101 B> 10^4a+20 0 10^4a+18 0 10^3 0 10^4a+4b+53 0 10^8 0^inf
                        rule_step(19, &[("a", "2a+8"), ("b", "2a+8"), ("c", "2a+2b+26")]),
                        // 0^inf 1100101 B> 10^4a+24 0 10^4a+22 1100 10^4a+4b+52 0 10^7 0^inf
                        rule_step(20, &[("a", "2a+11"), ("b", "2a+11"), ("c", "2a+2b+25"), ("d", "6")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+23 01100 10^8a+4b+73 0 10^7 0^inf
                        rule_step(21, &[("a", "3"), ("b", "2a+9"), ("c", "4a+2b+36"), ("d", "3")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4a+19 0 10^8a+4b+79 0 10^4 0^inf
                        rule_step(86, &[("a", "3"), ("b", "1"), ("c", "2a+9"), ("d", "4a+2b+37")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4 01100 10^4a+21 0 10^8a+4b+81 0^inf
                        rule_step(87, &[("a", "3"), ("b", "3"), ("c", "0"), ("d", "2a+10"), ("e", "8a+4b+77")]),
                        // 0^inf 1100101 B> 10^12 01100 10^9 0 10^3 0 10^4a+27 0 10^8a+4b+78 0^inf
                        rule_step(15, &[("a", "4"), ("b", "0"), ("c", "4")]),
                        // 0^inf 1100101 B> 10^16 0 10^14 00 10^4a+27 0 10^8a+4b+78 0^inf
                        rule_step(65, &[("a", "7"), ("b", "6"), ("c", "2a+13"), ("d", "8a+4b+76")]),
                        // 0^inf 1100101 B> 10^20 01100 10^4a+41 0 10^8a+4b+77 0^inf
                        rule_step(15, &[("a", "8"), ("b", "0"), ("c", "2a+20")]),
                        // 0^inf 1100101 B> 10^24 0 10^4a+46 0 10^8a+4b+74 0^inf
                        rule_step(10, &[("a", "10"), ("b", "2a+22"), ("c", "2"), ("n", "2a+b+18")]),
                        // 0^inf 1100101 B> 10^8a+4b+96 0 10^12a+4b+118 0 10^2 0^inf
                        rule_step(11, &[("a", "4a+2b+47"), ("b", "6a+2b+58")]),
                        // 0^inf 1100101 B> 10^8a+4b+100 01100 10^12a+4b+118 0^inf
                        rule_step(12, &[("a", "4a+2b+49"), ("b", "0"), ("c", "12a+4b+116")]),
                        // 0^inf 1100101 B> 10^8 0 10^8a+4b+99 01100 10^12a+4b+117 0^inf
                        rule_step(13, &[("a", "3"), ("b", "4a+2b+49"), ("c", "0"), ("d", "12a+4b+115")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^8a+4b+100 01100 10^12a+4b+116 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "2a+b+25")]),
                        // 0^inf 1100101 B> 10^8a+4b+108 0 10^8a+4b+106 001100 10^12a+4b+116 0^inf
                    ]),
                },
                // 107: B(a, 2b+1, 8)  -->  A(3a+b+34, 3a+b+34, 20a+8b+182)
                Rule {
                    init_config: b("a", "2b+1", "8"),
                    final_config: a("3a+b+34", "3a+b+34", "20a+8b+182"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^4a+4 0 10^4b+36 0 10^2 0 10^9 0^inf
                        rule_step(53, &[("a", "2a+1"), ("b", "2b+17"), ("c", "7")]),
                        // 0^inf 1100101 B> 10^4a+8 01100 10^4b+36 1100 10^8 0^inf
                        rule_step(81, &[("a", "2a+2"), ("b", "2b+17"), ("c", "1")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+7 0 10^4b+37 0 10^9 0 10^2 0^inf
                        rule_step(48, &[("a", "3"), ("b", "2a+3"), ("c", "2b+18"), ("d", "4"), ("e", "1")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+7 0 10^4b+37 0 10^9 0 10^2 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "a+1")]),
                        // 0^inf 1100101 B> 10^4a+12 0 10^4a+10 0 10^3 0 10^4b+37 0 10^9 0 10^2 0^inf
                        rule_step(19, &[("a", "2a+4"), ("b", "2a+4"), ("c", "2b+18")]),
                        // 0^inf 1100101 B> 10^4a+16 0 10^4a+14 1100 10^4b+36 0 10^8 0 10^2 0^inf
                        rule_step(85, &[("a", "2a+6"), ("b", "2a+7"), ("c", "2b+17"), ("d", "3")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+15 0 10^4a+4b+55 0 10^8 0^inf
                        rule_step(18, &[("a", "3"), ("b", "2a+7"), ("c", "2a+2b+27"), ("d", "7")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+15 0 10^4a+4b+55 0 10^8 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "a+3")]),
                        // 0^inf 1100101 B> 10^4a+20 0 10^4a+18 0 10^3 0 10^4a+4b+55 0 10^8 0^inf
                        rule_step(19, &[("a", "2a+8"), ("b", "2a+8"), ("c", "2a+2b+27")]),
                        // 0^inf 1100101 B> 10^4a+24 0 10^4a+22 1100 10^4a+4b+54 0 10^7 0^inf
                        rule_step(20, &[("a", "2a+11"), ("b", "2a+11"), ("c", "2a+2b+26"), ("d", "6")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+23 01100 10^8a+4b+75 0 10^7 0^inf
                        rule_step(21, &[("a", "3"), ("b", "2a+9"), ("c", "4a+2b+37"), ("d", "3")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4a+19 0 10^8a+4b+81 0 10^4 0^inf
                        rule_step(86, &[("a", "3"), ("b", "1"), ("c", "2a+9"), ("d", "4a+2b+38")]),
                        // 0^inf 1100101 B> 10^8 0 10^7 01100 10^4 01100 10^4a+21 0 10^8a+4b+83 0^inf
                        rule_step(87, &[("a", "3"), ("b", "3"), ("c", "0"), ("d", "2a+10"), ("e", "8a+4b+79")]),
                        // 0^inf 1100101 B> 10^12 01100 10^9 0 10^3 0 10^4a+27 0 10^8a+4b+80 0^inf
                        rule_step(15, &[("a", "4"), ("b", "0"), ("c", "4")]),
                        // 0^inf 1100101 B> 10^16 0 10^14 00 10^4a+27 0 10^8a+4b+80 0^inf
                        rule_step(65, &[("a", "7"), ("b", "6"), ("c", "2a+13"), ("d", "8a+4b+78")]),
                        // 0^inf 1100101 B> 10^20 01100 10^4a+41 0 10^8a+4b+79 0^inf
                        rule_step(15, &[("a", "8"), ("b", "0"), ("c", "2a+20")]),
                        // 0^inf 1100101 B> 10^24 0 10^4a+46 0 10^8a+4b+76 0^inf
                        rule_step(10, &[("a", "10"), ("b", "2a+22"), ("c", "0"), ("n", "2a+b+19")]),
                        // 0^inf 1100101 B> 10^8a+4b+100 0 10^12a+4b+122 0^inf
                        rule_step(9, &[("a", "4a+2b+49"), ("b", "12a+4b+121")]),
                        // 0^inf 1100101 B> 10^8 0 10^8a+4b+98 0 10^12a+4b+122 0^inf
                        rule_step(10, &[("a", "2"), ("b", "4a+2b+48"), ("c", "2"), ("n", "3a+b+30")]),
                        // 0^inf 1100101 B> 10^12a+4b+128 0 10^20a+8b+218 0 10^2 0^inf
                        rule_step(11, &[("a", "6a+2b+63"), ("b", "10a+4b+108")]),
                        // 0^inf 1100101 B> 10^12a+4b+132 01100 10^20a+8b+218 0^inf
                        rule_step(12, &[("a", "6a+2b+65"), ("b", "0"), ("c", "20a+8b+216")]),
                        // 0^inf 1100101 B> 10^8 0 10^12a+4b+131 01100 10^20a+8b+217 0^inf
                        rule_step(13, &[("a", "3"), ("b", "6a+2b+65"), ("c", "0"), ("d", "20a+8b+215")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^12a+4b+132 01100 10^20a+8b+216 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "3a+b+33")]),
                        // 0^inf 1100101 B> 10^12a+4b+140 0 10^12a+4b+138 001100 10^20a+8b+216 0^inf
                    ]),
                },
                // 108: B(a, b, 9)  -->  A(a+13, a+13, 8a+2b+48)
                Rule {
                    init_config: b("a", "b", "9"),
                    final_config: a("a+13", "a+13", "8a+2b+48"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^4a+4 0 10^2b+34 0 10^2 0 10^10 0^inf
                        rule_step(53, &[("a", "2a+1"), ("b", "b+16"), ("c", "8")]),
                        // 0^inf 1100101 B> 10^4a+8 01100 10^2b+34 1100 10^9 0^inf
                        rule_step(81, &[("a", "2a+2"), ("b", "b+16"), ("c", "2")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+7 0 10^2b+35 0 10^9 0 10^3 0^inf
                        rule_step(48, &[("a", "3"), ("b", "2a+3"), ("c", "b+17"), ("d", "4"), ("e", "2")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+7 0 10^2b+35 0 10^9 0 10^3 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "a+1")]),
                        // 0^inf 1100101 B> 10^4a+12 0 10^4a+10 0 10^3 0 10^2b+35 0 10^9 0 10^3 0^inf
                        rule_step(19, &[("a", "2a+4"), ("b", "2a+4"), ("c", "b+17")]),
                        // 0^inf 1100101 B> 10^4a+16 0 10^4a+14 1100 10^2b+34 0 10^8 0 10^3 0^inf
                        rule_step(88, &[("a", "2a+7"), ("b", "2a+7"), ("c", "b+15"), ("d", "3")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+15 01100 10^4a+2b+48 0 10^10 0^inf
                        rule_step(63, &[("a", "3"), ("b", "2a+7"), ("c", "2a+b+23"), ("d", "9")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+16 01100 10^4a+2b+47 0 10^10 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "a+4")]),
                        // 0^inf 1100101 B> 10^4a+24 0 10^4a+22 001100 10^4a+2b+47 0 10^10 0^inf
                        rule_step(64, &[("a", "2a+11"), ("b", "2a+11"), ("c", "2a+b+22"), ("d", "9")]),
                        // 0^inf 1100101 B> 10^4a+28 01100 10^4a+25 0 10^3 0 10^4a+2b+45 0 10^10 0^inf
                        rule_step(15, &[("a", "2a+12"), ("b", "0"), ("c", "2a+12")]),
                        // 0^inf 1100101 B> 10^4a+32 0 10^4a+30 00 10^4a+2b+45 0 10^10 0^inf
                        rule_step(65, &[("a", "2a+15"), ("b", "2a+14"), ("c", "2a+b+22"), ("d", "8")]),
                        // 0^inf 1100101 B> 10^4a+36 01100 10^8a+2b+75 0 10^9 0^inf
                        rule_step(15, &[("a", "2a+16"), ("b", "0"), ("c", "4a+b+37")]),
                        // 0^inf 1100101 B> 10^4a+40 0 10^8a+2b+80 0 10^6 0^inf
                        rule_step(10, &[("a", "2a+18"), ("b", "4a+b+39"), ("c", "2"), ("n", "1")]),
                        // 0^inf 1100101 B> 10^4a+44 0 10^8a+2b+84 0 10^2 0^inf
                        rule_step(11, &[("a", "2a+21"), ("b", "4a+b+41")]),
                        // 0^inf 1100101 B> 10^4a+48 01100 10^8a+2b+84 0^inf
                        rule_step(12, &[("a", "2a+23"), ("b", "0"), ("c", "8a+2b+82")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+47 01100 10^8a+2b+83 0^inf
                        rule_step(13, &[("a", "3"), ("b", "2a+23"), ("c", "0"), ("d", "8a+2b+81")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+48 01100 10^8a+2b+82 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "a+12")]),
                        // 0^inf 1100101 B> 10^4a+56 0 10^4a+54 001100 10^8a+2b+82 0^inf
                    ]),
                },
                // 109: B(a, b, 10)  -->  A(a+10, a+10, 4a+2b+24)
                Rule {
                    init_config: b("a", "b", "10"),
                    final_config: a("a+10", "a+10", "4a+2b+24"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^4a+4 0 10^2b+34 0 10^2 0 10^11 0^inf
                        rule_step(53, &[("a", "2a+1"), ("b", "b+16"), ("c", "9")]),
                        // 0^inf 1100101 B> 10^4a+8 01100 10^2b+34 1100 10^10 0^inf
                        rule_step(81, &[("a", "2a+2"), ("b", "b+16"), ("c", "3")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+7 0 10^2b+35 0 10^9 0 10^4 0^inf
                        rule_step(48, &[("a", "3"), ("b", "2a+3"), ("c", "b+17"), ("d", "4"), ("e", "3")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+7 0 10^2b+35 0 10^9 0 10^4 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "a+1")]),
                        // 0^inf 1100101 B> 10^4a+12 0 10^4a+10 0 10^3 0 10^2b+35 0 10^9 0 10^4 0^inf
                        rule_step(19, &[("a", "2a+4"), ("b", "2a+4"), ("c", "b+17")]),
                        // 0^inf 1100101 B> 10^4a+16 0 10^4a+14 1100 10^2b+34 0 10^8 0 10^4 0^inf
                        rule_step(89, &[("a", "2a+7"), ("b", "2a+7"), ("c", "b+15"), ("d", "3")]),
                        // 0^inf 1100101 B> 10^4a+20 01100 10^4a+2b+47 0 10^13 0^inf
                        rule_step(15, &[("a", "2a+8"), ("b", "0"), ("c", "2a+b+23")]),
                        // 0^inf 1100101 B> 10^4a+24 0 10^4a+2b+52 0 10^10 0^inf
                        rule_step(10, &[("a", "2a+10"), ("b", "2a+b+25"), ("c", "2"), ("n", "2")]),
                        // 0^inf 1100101 B> 10^4a+32 0 10^4a+2b+60 0 10^2 0^inf
                        rule_step(11, &[("a", "2a+15"), ("b", "2a+b+29")]),
                        // 0^inf 1100101 B> 10^4a+36 01100 10^4a+2b+60 0^inf
                        rule_step(12, &[("a", "2a+17"), ("b", "0"), ("c", "4a+2b+58")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+35 01100 10^4a+2b+59 0^inf
                        rule_step(13, &[("a", "3"), ("b", "2a+17"), ("c", "0"), ("d", "4a+2b+57")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+36 01100 10^4a+2b+58 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "0"), ("n", "a+9")]),
                        // 0^inf 1100101 B> 10^4a+44 0 10^4a+42 001100 10^4a+2b+58 0^inf
                    ]),
                },
                // 110: B(a, b, c+11)  -->  B(a+7, 2a+b+13, c)
                Rule {
                    init_config: b("a", "b", "c+11"),
                    final_config: b("a+7", "2a+b+13", "c"),
                    proof: Proof::Simple(vec![
                        // 0^inf 1100101 B> 10^4a+4 0 10^2b+34 0 10^2 0 10^c+12 0^inf
                        rule_step(53, &[("a", "2a+1"), ("b", "b+16"), ("c", "c+10")]),
                        // 0^inf 1100101 B> 10^4a+8 01100 10^2b+34 1100 10^c+11 0^inf
                        rule_step(81, &[("a", "2a+2"), ("b", "b+16"), ("c", "c+4")]),
                        // 0^inf 1100101 B> 10^8 0 10^4a+7 0 10^2b+35 0 10^9 0 10^c+5 0^inf
                        rule_step(48, &[("a", "3"), ("b", "2a+3"), ("c", "b+17"), ("d", "4"), ("e", "c+4")]),
                        // 0^inf 1100101 B> 10^8 0 10^6 0 10^4a+7 0 10^2b+35 0 10^9 0 10^c+5 0^inf
                        rule_step(10, &[("a", "2"), ("b", "2"), ("c", "3"), ("n", "a+1")]),
                        // 0^inf 1100101 B> 10^4a+12 0 10^4a+10 0 10^3 0 10^2b+35 0 10^9 0 10^c+5 0^inf
                        rule_step(19, &[("a", "2a+4"), ("b", "2a+4"), ("c", "b+17")]),
                        // 0^inf 1100101 B> 10^4a+16 0 10^4a+14 1100 10^2b+34 0 10^8 0 10^c+5 0^inf
                        rule_step(49, &[("a", "2a+7"), ("b", "2a+7"), ("c", "b+15"), ("d", "3"), ("e", "c")]),
                        // 0^inf 1100101 B> 10^4a+20 01100 10^4a+2b+47 0 10^13 0 10^c+1 0^inf
                        rule_step(15, &[("a", "2a+8"), ("b", "0"), ("c", "2a+b+23")]),
                        // 0^inf 1100101 B> 10^4a+24 0 10^4a+2b+52 0 10^10 0 10^c+1 0^inf
                        rule_step(10, &[("a", "2a+10"), ("b", "2a+b+25"), ("c", "2"), ("n", "2")]),
                        // 0^inf 1100101 B> 10^4a+32 0 10^4a+2b+60 0 10^2 0 10^c+1 0^inf
                    ]),
                },
            ],
        };
        if let Err(err) = validate_rule_set(&rule_set) {
            panic!("{}", err);
        }
    }
}
