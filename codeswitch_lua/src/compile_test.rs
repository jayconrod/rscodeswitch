use crate::compile::compile_file_data;

use std::path::PathBuf;

#[test]
fn test_disable_control() {
    let src = b"print(\"poison\")";
    assert!(compiled_package_contains_string(src, b"poison"));
}

#[test]
fn test_return_disable() {
    let src = b"
        do return end
        print(\"poison\")
    ";
    assert!(!compiled_package_contains_string(src, b"poison"));
}

#[test]
fn test_if_return_some_branch_disable() {
    let src = b"
        if true then
            return
        else
            print(\"ok\")
        end
        print(\"poison\")
    ";
    assert!(compiled_package_contains_string(src, b"poison"));
}

#[test]
fn test_if_return_all_branch_disable() {
    let src = b"
        if true then
            return
        else
            return
        end
        print(\"poison\")
    ";
    assert!(!compiled_package_contains_string(src, b"poison"));
}

#[test]
fn test_while_break_disable() {
    let src = b"
        while true do
            break
            print(\"poison\")
        end
    ";
    assert!(!compiled_package_contains_string(src, b"poison"));
}

#[test]
fn test_repeat_break_disable() {
    let src = b"
        repeat
            break
            print(\"poison\")
        until true
    ";
    assert!(!compiled_package_contains_string(src, b"poison"));
}

#[test]
fn test_for_break_disable() {
    let src = b"
        for i = 1, 2 do
            break
            print(\"poison\")
        end
    ";
    assert!(!compiled_package_contains_string(src, b"poison"));
}

#[test]
fn test_for_in_break_disable() {
    let src = b"
        for k, v in pairs({}) do
            break
            print(\"poison\")
        end
    ";
    assert!(!compiled_package_contains_string(src, b"poison"));
}

#[test]
fn test_goto_disable() {
    let src = b"
        goto a
        print(\"poison\")
        ::a::
    ";
    assert!(!compiled_package_contains_string(src, b"poison"));
}

#[test]
fn test_label_enable() {
    let src = b"
        goto a
        ::b::
        print(\"poison\")
        do return end
        ::a::
        goto b
    ";
    assert!(compiled_package_contains_string(src, b"poison"));
}

/// Checks whether the package compiled from the given source contains the
/// string "poison". Tests use this to check whether code generation is
/// correctly disabled after a statement like return or break.
fn compiled_package_contains_string(data: &[u8], needle: &[u8]) -> bool {
    let path = PathBuf::from("test");
    let package = compile_file_data(&path, data).unwrap();
    package.strings.iter().any(|s| s == needle)
}
