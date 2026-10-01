//! The agent skill (`skills/outliner/SKILL.md`) agrees with the Python API it
//! describes (`dist/outliner/api.py`) and can be used by Sidekick, which
//! renders a skill's body as a Jinja template.

const SKILL: &str = include_str!("../../../skills/outliner/SKILL.md");
const API: &str = include_str!("../../../dist/outliner/api.py");
const PACKAGE: &str = include_str!("../../../dist/outliner/__init__.py");

#[test]
fn the_skill_has_a_name_and_a_description() {
    let header = SKILL.strip_prefix("---\n").expect("the skill starts with a YAML header");
    let (header, body) = header.split_once("\n---\n").expect("the header ends with ---");
    assert!(header.lines().any(|l| l == "name: outliner"), "{header}");
    let description = header.lines().find_map(|l| l.strip_prefix("description: ")).expect("a description");
    assert!(description.len() > 40, "{description}");
    assert!(body.trim_start().starts_with("# Outliner"));
}

#[test]
fn the_skill_renders_unchanged_as_a_template() {
    for delimiter in ["{{", "{%", "{#", "}}", "%}", "#}"] {
        assert!(!SKILL.contains(delimiter), "the skill contains {delimiter}, which Sidekick reads as template syntax");
    }
}

#[test]
fn every_call_the_skill_names_exists() {
    let exported: Vec<&str> = API
        .split("__all__ = [")
        .nth(1)
        .and_then(|rest| rest.split(']').next())
        .expect("api.py lists __all__")
        .split(',')
        .map(|name| name.trim().trim_matches('"'))
        .filter(|name| !name.is_empty())
        .collect();
    let mut named = Vec::new();
    let mut rest = SKILL;
    while let Some(at) = rest.find("outliner.") {
        rest = &rest[at + "outliner.".len()..];
        let name: String = rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
        if !name.is_empty() && rest[name.len()..].starts_with('(') {
            named.push(name);
        }
    }
    assert!(named.len() > 10, "{named:?}");
    for name in &named {
        let defined = exported.contains(&name.as_str()) || PACKAGE.contains(&format!("import {name}"));
        assert!(defined, "the skill calls outliner.{name}, which the Python API does not export");
        assert!(API.contains(&format!("def {name}(")) || PACKAGE.contains(name.as_str()), "outliner.{name} is exported but not defined");
    }
}
