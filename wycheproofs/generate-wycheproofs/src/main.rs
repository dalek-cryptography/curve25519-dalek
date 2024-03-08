use codegen::Scope;
use itertools::Itertools;
use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
use std::path::Path;

fn usage(code: i32) -> ! {
    eprintln!("Usage: cargo run --bin generate-wycheproofs [ed25519|..]");
    std::process::exit(code)
}

#[derive(Debug, Eq, PartialEq, Hash, Clone, Ord, PartialOrd)]
enum TestExpectation {
    Valid,
    Invalid,
    Acceptable,
}

impl From<wycheproof::TestResult> for TestExpectation {
    fn from(res: wycheproof::TestResult) -> TestExpectation {
        match res {
            wycheproof::TestResult::Valid => TestExpectation::Valid,
            wycheproof::TestResult::Invalid => TestExpectation::Invalid,
            wycheproof::TestResult::Acceptable => TestExpectation::Acceptable,
        }
    }
}

use std::fmt::Display;

mod generator_ed25519 {

    use super::*;

    #[derive(Debug, Eq, PartialEq, Hash, Clone, Ord, PartialOrd)]
    struct Ed25519tc {
        tc_id: usize,
        input_public_key_hexstring: String,
        input_signature_hexstring: String,
        input_msg_hexstring: String,
        comment: String,
        expect: TestExpectation,
    }

    struct Ed25519tcs {
        tc: HashMap<usize, Ed25519tc>,
    }

    impl Display for Ed25519tcs {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
            let tcs: Vec<_> = self.tc.iter().sorted().collect();
            write!(
                f,
                "{}",
                tcs.into_iter().map(|a| a.1.to_string()).join("\n\n")
            )
        }
    }

    impl Display for Ed25519tc {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
            let mut scope = Scope::new();

            let tc_name = format!("wycheproof_tc_{}", self.tc_id);

            let test_fn = scope
                .new_fn(&tc_name)
                .attr("test")
                .doc(format!("wycheproofs TC[{}] {}", self.tc_id, self.comment));

            test_fn.line(format!(
                "super::ed25519_dalek_wycheproof(\"{}\", \"{}\", \"{}\")",
                self.input_public_key_hexstring,
                self.input_signature_hexstring,
                self.input_msg_hexstring
            ));

            match self.expect {
                TestExpectation::Valid => {}
                _ => {
                    test_fn.attr("should_panic");
                }
            }

            write!(f, "{}", scope.to_string())
        }
    }

    pub fn run() {
        let p = Path::new("./wycheproofs/wycheproof-ed25519-dalek/src");

        if !p.exists() {
            eprintln!("Run this from top level directory");
            usage(2)
        }

        let mut gen_tests = Ed25519tcs { tc: HashMap::new() };

        let test_set =
            wycheproof::eddsa::TestSet::load(wycheproof::eddsa::TestName::Ed25519).unwrap();
        for test_group in test_set.test_groups {
            let wycheproof::EddsaPublic { pk, .. } = test_group.key;
            for test in test_group.tests {
                gen_tests.tc.insert(
                    test.tc_id,
                    Ed25519tc {
                        tc_id: test.tc_id,
                        input_public_key_hexstring: hex::encode(pk.clone()),
                        input_signature_hexstring: hex::encode(test.sig),
                        input_msg_hexstring: hex::encode(test.msg),
                        comment: test.comment,
                        expect: test.result.into(),
                    },
                );
            }
        }

        let full_p = p.join("generated.rs");

        let mut file = File::create(full_p).expect("Could not create generated.rs");

        file.write_all(gen_tests.to_string().as_bytes())
            .expect("Failed to write the generated output.");
    }
}

fn main() {
    match std::env::args().last().unwrap().as_str() {
        "ed25519" => generator_ed25519::run(),
        _ => usage(1),
    }
}
