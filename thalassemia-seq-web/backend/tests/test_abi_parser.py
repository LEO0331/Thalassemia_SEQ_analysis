from lib.abi_parser import parse_ab1


def test_parse_ab1_invalid_file_raises_clean_error() -> None:
    bad_bytes = b"not-an-ab1-file"
    try:
        parse_ab1(bad_bytes)
    except ValueError as exc:
        assert "Invalid or unsupported .ab1 file." in str(exc)
    else:
        raise AssertionError("parse_ab1 should raise ValueError for invalid file")
