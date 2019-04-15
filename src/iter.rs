//! Iterators over a `Rope`'s data.
//!
//! All iterators here can also be used with `RopeSlice`'s.  When used
//! with a `RopeSlice`, they iterate over only the data that the
//! `RopeSlice` refers to.  For the line and chunk, iterators, the data
//! of the first and last yielded item will be truncated to match the
//! `RopeSlice`.

use std::fmt;
use std::iter::FusedIterator;
use std::ops::Range;
use std::str;
use std::sync::Arc;

use slice::RopeSlice;
use str_utils::{
    char_to_byte_idx, char_to_line_idx, count_line_breaks, ends_with_line_break, line_to_byte_idx,
    line_to_char_idx, reverse_line_to_byte_idx,
};
use tree::Node;

//==========================================================

/// An iterator over a `Rope`'s bytes.
pub struct Bytes<'a> {
    chunk_iter: Chunks<'a>,
    cur_chunk: str::Bytes<'a>,
}

impl<'a> Bytes<'a> {
    pub(crate) fn new(node: &Arc<Node>) -> Bytes {
        Bytes {
            chunk_iter: Chunks::new(node),
            cur_chunk: "".bytes(),
        }
    }

    pub(crate) fn new_with_range(node: &Arc<Node>, start_char: usize, end_char: usize) -> Bytes {
        Bytes {
            chunk_iter: Chunks::new_with_range(node, start_char, end_char),
            cur_chunk: "".bytes(),
        }
    }

    pub(crate) fn from_str(text: &str) -> Bytes {
        Bytes {
            chunk_iter: Chunks::new_empty(),
            cur_chunk: text.bytes(),
        }
    }
}

impl<'a> Iterator for Bytes<'a> {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        loop {
            if let Some(c) = self.cur_chunk.next() {
                return Some(c);
            } else if let Some(chunk) = self.chunk_iter.next() {
                self.cur_chunk = chunk.bytes();
                continue;
            } else {
                return None;
            }
        }
    }
}

//==========================================================

/// An iterator over a `Rope`'s chars.
pub struct Chars<'a> {
    chunk_iter: Chunks<'a>,
    cur_chunk: str::Chars<'a>,
}

impl<'a> Chars<'a> {
    pub(crate) fn new(node: &Arc<Node>) -> Chars {
        Chars {
            chunk_iter: Chunks::new(node),
            cur_chunk: "".chars(),
        }
    }

    pub(crate) fn new_with_range(node: &Arc<Node>, start_char: usize, end_char: usize) -> Chars {
        Chars {
            chunk_iter: Chunks::new_with_range(node, start_char, end_char),
            cur_chunk: "".chars(),
        }
    }

    pub(crate) fn from_str(text: &str) -> Chars {
        Chars {
            chunk_iter: Chunks::new_empty(),
            cur_chunk: text.chars(),
        }
    }
}

impl<'a> Iterator for Chars<'a> {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        loop {
            if let Some(c) = self.cur_chunk.next() {
                return Some(c);
            } else if let Some(chunk) = self.chunk_iter.next() {
                self.cur_chunk = chunk.chars();
                continue;
            } else {
                return None;
            }
        }
    }
}

impl<'a> FusedIterator for Chars<'a> {}

//==========================================================

/// An iterator over a `Rope`'s lines.
///
/// The returned lines include the line-break at the end.
///
/// The last line is returned even if blank, in which case it
/// is returned as an empty slice.
#[derive(Clone)]
pub struct Lines<'a> {
    variant: LinesEnum<'a>,
}

#[derive(Clone)]
enum LinesEnum<'a> {
    Full {
        node: &'a Arc<Node>,
        start_char: usize,
        end_char: usize,
        // The next line
        line_idx: usize,
        // The next reversed line
        rev_line_idx: usize,
    },
    Light {
        text: &'a str,
        // line_idx maybe > Option(rev_line_idx).
        // text empty returns None.
        line_idx: usize,
        // The number of lines in the `text` is lazily calculated
        rev_line_idx: usize,
    },
}

impl<'a> Lines<'a> {
    pub(crate) fn new(node: &Arc<Node>) -> Lines {
        let end_char = node.text_info().chars as usize;
        Lines {
            variant: LinesEnum::Full {
                node,
                start_char: 0,
                end_char,
                line_idx: 0,
                rev_line_idx: node.line_break_count()
                    + !full_ends_with_line_break(node, end_char) as usize,
            },
        }
    }

    pub(crate) fn new_with_range(node: &Arc<Node>, start_char: usize, end_char: usize) -> Lines {
        Lines {
            variant: LinesEnum::Full {
                node: node,
                start_char,
                end_char,
                line_idx: {
                    let (chunk, _, c, l) = node.get_chunk_at_char(start_char);
                    l + char_to_line_idx(chunk, start_char - c)
                },
                rev_line_idx: {
                    let (chunk, _, c, l) = node.get_chunk_at_char(end_char);
                    l + char_to_line_idx(chunk, end_char - c)
                } + !full_ends_with_line_break(node, end_char) as usize,
            },
        }
    }

    /// Caller guaranties `line_break_count` is accurate/consistent with `str_utils::count_line_breaks`.
    /// If you do not know the `line_break_count` use `Lines::from` instead.
    pub fn from_str(text: &str, line_break_count: usize) -> Lines {
        Lines {
            variant: LinesEnum::Light {
                text: text,
                line_idx: 0,
                rev_line_idx: line_break_count + !ends_with_line_break(text) as usize,
            },
        }
    }

    /// Narrows the slice of lines to be iterated over.
    /// The `lines` argument describes a range within the lines that have yet to be iterated over.
    pub fn narrow(mut self, lines: Range<usize>) -> Self {
        match &mut self.variant {
            LinesEnum::Full {
                line_idx,
                rev_line_idx,
                ..
            } => {
                *rev_line_idx = (*rev_line_idx).min(lines.end - 1 + *line_idx);
                *line_idx = (*rev_line_idx).min(lines.start + *line_idx);
            }
            LinesEnum::Light { text, line_idx, .. } => {
                *line_idx += lines.start;
                let split_idx = line_to_byte_idx(text, lines.start).byte_idx;
                let start_text = &text[split_idx..];

                let split_idx = line_to_byte_idx(start_text, lines.end - lines.start).byte_idx;
                *text = &start_text[..split_idx];
            }
        }
        self
    }
}

#[inline]
fn full_nth<'a>(
    n: usize,
    node: &'a Arc<Node>,
    start_char: usize,
    end_char: usize,
    line_idx: &mut usize,
    rev_line_idx: usize,
) -> Option<RopeSlice<'a>> {
    let nth_idx = *line_idx + n;
    if nth_idx > rev_line_idx {
        return None;
    } else {
        let a = {
            // Find the char that corresponds to the start of the line.
            let (chunk, _, c, l) = node.get_chunk_at_line_break(nth_idx);
            (c + line_to_char_idx(chunk, nth_idx - l)).max(start_char)
        };
        // Early out if we're past the specified end char
        if a >= end_char {
            *line_idx = rev_line_idx + 1;
            return None;
        }

        let b = {
            // Find the char that corresponds to the end of the line.
            let (chunk, _, c, l) = node.get_chunk_at_line_break(nth_idx + 1);
            end_char.min(c + line_to_char_idx(chunk, nth_idx + 1 - l))
        };

        *line_idx = nth_idx + 1;

        return Some(RopeSlice::new_with_range(node, a, b));
    }
}

impl<'a> Iterator for Lines<'a> {
    type Item = RopeSlice<'a>;

    fn next(&mut self) -> Option<RopeSlice<'a>> {
        match self.variant {
            LinesEnum::Full {
                ref mut node,
                start_char,
                end_char,
                ref mut line_idx,
                rev_line_idx,
            } => full_nth(0, node, start_char, end_char, line_idx, rev_line_idx),
            LinesEnum::Light {
                ref mut text,
                ref mut line_idx,
                ..
            } => {
                if text.is_empty() {
                    return None;
                } else {
                    *line_idx += 1;
                    let split_idx = line_to_byte_idx(text, 1).byte_idx;
                    let t = &text[..split_idx];
                    *text = &text[split_idx..];
                    return Some(t.into());
                }
            }
        }
    }

    fn nth(&mut self, n: usize) -> Option<RopeSlice<'a>> {
        match self.variant {
            LinesEnum::Full {
                node,
                start_char,
                end_char,
                ref mut line_idx,
                rev_line_idx,
            } => full_nth(n, node, start_char, end_char, line_idx, rev_line_idx),
            LinesEnum::Light {
                ref mut text,
                ref mut line_idx,
                ..
            } => {
                *line_idx += 1 + n;
                if text.is_empty() {
                    return None;
                } else {
                    let start_idx = line_to_byte_idx(text, n).byte_idx;
                    let start_text = &text[start_idx..];
                    if start_text.is_empty() {
                        *text = "";
                        return None;
                    }

                    let end_idx = line_to_byte_idx(start_text, 1).byte_idx;
                    let nth_line = &start_text[..end_idx];
                    *text = &start_text[end_idx..];
                    return Some(nth_line.into());
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.variant {
            LinesEnum::Full {
                line_idx,
                rev_line_idx,
                ..
            } => {
                // If the RopeSlice does not end with a line-break it is one longer.
                // For the upper bound we fallback to assuming the longer variant.
                let len = rev_line_idx - rev_line_idx.min(line_idx);
                (len, Some(len))
            }
            LinesEnum::Light {
                line_idx,
                rev_line_idx,
                text,
                ..
            } => {
                if text.is_empty() {
                    return (0, Some(0));
                }
                let len = rev_line_idx - rev_line_idx.min(line_idx);
                (len, Some(len))
            }
        }
    }
}

impl<'a> DoubleEndedIterator for Lines<'a> {
    fn next_back(&mut self) -> Option<RopeSlice<'a>> {
        match self.variant {
            LinesEnum::Full {
                node,
                start_char,
                end_char,
                ref mut line_idx,
                ref mut rev_line_idx,
            } => {
                // `next` uses `>` and a early return if `a >= end_char`.
                if *line_idx >= *rev_line_idx {
                    return None;
                } else {
                    let a = {
                        // Find the char that corresponds to the start of the line.
                        let (chunk, _, c, l) = node.get_chunk_at_line_break(*rev_line_idx - 1);
                        (c + line_to_char_idx(chunk, *rev_line_idx - 1 - l)).max(start_char)
                    };

                    let b = if *rev_line_idx <= node.line_break_count() {
                        // Find the char that corresponds to the end of the line.
                        let (chunk, _, c, l) = node.get_chunk_at_line_break(*rev_line_idx);
                        c + line_to_char_idx(chunk, *rev_line_idx - l)
                    } else {
                        node.char_count()
                    }
                    .min(end_char);

                    // Mark the Iterator as done by setting line_idx > rev_line_idx
                    if *rev_line_idx != *line_idx {
                        *rev_line_idx -= 1;
                    } else {
                        *line_idx += 1;
                    };

                    return Some(RopeSlice::new_with_range(node, a, b));
                }
            }
            LinesEnum::Light {
                ref mut text,
                ref mut rev_line_idx,
                ..
            } => {
                if text.is_empty() {
                    return None;
                } else {
                    *rev_line_idx -= 1;
                    let split_idx = reverse_line_to_byte_idx(text, 1);
                    let t = &text[split_idx..];
                    *text = &text[..split_idx];
                    return Some(t.into());
                }
            }
        }
    }
}

fn full_ends_with_line_break(node: &Arc<Node>, end_char: usize) -> bool {
    let (chunk, _, chunk_char_idx, _) = node.get_chunk_at_char(end_char);
    if chunk.is_empty() {
        return false;
    };
    match chunk.chars().nth(end_char - chunk_char_idx - 1).unwrap() {
        '\u{000A}' | '\u{000B}' | '\u{000C}' | '\u{000D}' | '\u{0085}' | '\u{2028}'
        | '\u{2029}' => true,
        _ => false,
    }
}

impl<'l> ExactSizeIterator for Lines<'l> {
    fn len(&self) -> usize {
        // A mutable reference is necessary for memorization of Light str length
        match self.variant {
            LinesEnum::Full {
                line_idx,
                rev_line_idx,
                ..
            } => rev_line_idx - rev_line_idx.min(line_idx),
            LinesEnum::Light {
                line_idx,
                rev_line_idx,
                text,
            } => {
                if text.is_empty() {
                    return 0;
                }

                rev_line_idx - rev_line_idx.min(line_idx)
            }
        }
    }
}

impl<'a> From<&'a str> for Lines<'a> {
    fn from(text: &str) -> Lines {
        Lines {
            variant: LinesEnum::Light {
                text: text,
                line_idx: 0,
                rev_line_idx: count_line_breaks(text) + !ends_with_line_break(text) as usize,
            },
        }
    }
}

impl<'a> From<&Lines<'a>> for RopeSlice<'a> {
    fn from(lines: &Lines<'a>) -> RopeSlice<'a> {
        match lines.variant {
            LinesEnum::Full {
                node,
                start_char,
                end_char,
                line_idx,
                rev_line_idx,
            } => {
                let a = {
                    // Find the char that corresponds to the start of the line.
                    let (chunk, _, c, l) = node.get_chunk_at_line_break(line_idx);
                    (c + line_to_char_idx(chunk, line_idx - l)).max(start_char)
                };
                // Early out if we're past the specified end char
                if a >= end_char {
                    return "".into();
                }

                let b = {
                    let (chunk, _, c, l) = node.get_chunk_at_line_break(rev_line_idx + 1);
                    (end_char).min(c + line_to_char_idx(chunk, rev_line_idx + 1 - l))
                };

                RopeSlice::new_with_range(node, a, b)
            }
            LinesEnum::Light { text, .. } => RopeSlice::from(text),
        }
    }
}

impl<'a> From<Lines<'a>> for RopeSlice<'a> {
    fn from(lines: Lines<'a>) -> RopeSlice<'a> {
        (&lines).into()
    }
}

impl<'a> PartialEq for Lines<'a> {
    fn eq(&self, rhs: &Self) -> bool {
        let mut left = self.clone();
        let mut right = rhs.clone();
        loop {
            let l = left.next();
            let r = right.next();
            match (l, r) {
                (Some(l), Some(r)) => {
                    if l != r {
                        return false;
                    }
                }
                (None, None) => break,
                _ => return false,
            }
        }
        return true;
    }
}

impl<'a> Eq for Lines<'a> {}
impl<'a> FusedIterator for Lines<'a> {}

impl<'a> fmt::Debug for Lines<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_list()
            .entries(self.clone().map(|l| l.chars().collect::<String>()))
            .finish()
    }
}

//==========================================================

/// An iterator over a `Rope`'s contiguous `str` chunks.
///
/// Internally, each `Rope` stores text as a segemented collection of utf8
/// strings. This iterator iterates over those segments, returning a
/// `&str` slice for each one.  It is useful for situations such as:
///
/// - Writing a rope's utf8 text data to disk (but see
///   [`Rope::write_to()`](../struct.Rope.html#method.write_to) for a
///   convenience function that does this).
/// - Streaming a rope's text data somewhere.
/// - Saving a rope to a non-utf8 encoding, doing the encoding conversion
///   incrementally as you go.
/// - Writing custom iterators over a rope's text data.
///
/// There are precisely two guarantees about the yielded chunks:
///
/// - All chunks are yielded, and they are yielded in order.
/// - CRLF pairs are never split across chunks.
///
/// There are no guarantees about the size of yielded chunks, and except for
/// CRLF pairs there are no guarantees about where the chunks are split.  For
/// example, they may be zero-sized, they don't necessarily align with line
/// breaks, etc.
pub struct Chunks<'a>(ChunksEnum<'a>);

enum ChunksEnum<'a> {
    Full {
        node_stack: Vec<&'a Arc<Node>>,
        start: usize,
        end: usize,
        idx: usize,
    },
    Light {
        text: &'a str,
    },
}

impl<'a> Chunks<'a> {
    pub(crate) fn new(node: &Arc<Node>) -> Chunks {
        Chunks(ChunksEnum::Full {
            node_stack: vec![node],
            start: 0,
            end: node.text_info().bytes as usize,
            idx: 0,
        })
    }

    pub(crate) fn new_empty() -> Chunks<'static> {
        Chunks(ChunksEnum::Light { text: "" })
    }

    pub(crate) fn new_with_range(node: &Arc<Node>, start_char: usize, end_char: usize) -> Chunks {
        let start_byte = {
            let (chunk, b, c, _) = node.get_chunk_at_char(start_char);
            b + char_to_byte_idx(chunk, start_char - c)
        };
        let end_byte = {
            let (chunk, b, c, _) = node.get_chunk_at_char(end_char);
            b + char_to_byte_idx(chunk, end_char - c)
        };
        Chunks(ChunksEnum::Full {
            node_stack: vec![node],
            start: start_byte,
            end: end_byte,
            idx: 0,
        })
    }

    pub(crate) fn from_str(text: &str) -> Chunks {
        Chunks(ChunksEnum::Light { text: text })
    }
}

impl<'a> Iterator for Chunks<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        match *self {
            Chunks(ChunksEnum::Full {
                ref mut node_stack,
                start,
                end,
                ref mut idx,
            }) => {
                if *idx >= end {
                    return None;
                }

                loop {
                    if let Some(node) = node_stack.pop() {
                        match **node {
                            Node::Leaf(ref text) => {
                                let start_byte = if start <= *idx { 0 } else { start - *idx };
                                let end_byte = if end >= (*idx + text.len()) {
                                    text.len()
                                } else {
                                    end - *idx
                                };
                                *idx += text.len();
                                return Some(&text[start_byte..end_byte]);
                            }

                            Node::Internal(ref children) => {
                                // Find the first child that isn't before `start`,
                                // updating `idx` as we go.
                                let mut child_i = 0;
                                for inf in children.info().iter() {
                                    if (*idx + inf.bytes as usize) > start {
                                        break;
                                    } else {
                                        *idx += inf.bytes as usize;
                                        child_i += 1;
                                    }
                                }
                                // Push relevant children to the stack.
                                for child in (&children.nodes()[child_i..]).iter().rev() {
                                    node_stack.push(child);
                                }
                            }
                        }
                    } else {
                        return None;
                    }
                }
            }
            Chunks(ChunksEnum::Light { ref mut text }) => {
                if text.is_empty() {
                    return None;
                } else {
                    let t = *text;
                    *text = "";
                    return Some(t);
                }
            }
        }
    }
}

//===========================================================

#[cfg(test)]
mod tests {
    use std::fmt::Debug;

    use super::Lines;
    use Rope;
    use RopeSlice;

    const TEXT: &str = "\r\n\
                        Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?\r\n\
                        こんにちは！元気ですか？日はいいですね。\
                        私たちが生きだって嬉しいではないか？\r\n\
                        Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?\r\n\
                        こんにちは！元気ですか？日はいいですね。\
                        私たちが生きだって嬉しいではないか？\r\n\
                        Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?\r\n\
                        こんにちは！元気ですか？日はいいですね。\
                        私たちが生きだって嬉しいではないか？\r\n\
                        Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?\r\n\
                        こんにちは！元気ですか？日はいいですね。\
                        私たちが生きだって嬉しいではないか？\r\n\
                        Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?\r\n\
                        こんにちは！元気ですか？日はいいですね。\
                        私たちが生きだって嬉しいではないか？\r\n\
                        Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?\r\n\
                        こんにちは！元気ですか？日はいいですね。\
                        私たちが生きだって嬉しいではないか？\r\n\
                        Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?\r\n\
                        こんにちは！元気ですか？日はいいですね。\
                        私たちが生きだって嬉しいではないか？\r\n\
                        Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?\r\n\
                        こんにちは！元気ですか？日はいいですね。\
                        私たちが生きだって嬉しいではないか？\r\n\
                        Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?\r\n\
                        こんにちは！元気ですか？日はいいですね。\
                        私たちが生きだって嬉しいではないか？\r\n\
                        Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?\r\n\
                        こんにちは！元気ですか？日はいいですね。\
                        私たちが生きだって嬉しいではないか？\r\n\
                        Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?\r\n\
                        こんにちは！元気ですか？日はいいですね。\
                        私たちが生きだって嬉しいではないか？\r\n\
                        Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?\r\n\
                        こんにちは！元気ですか？日はいいですね。\
                        私たちが生きだって嬉しいではないか？\r\n\
                        Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?\r\n\
                        こんにちは！元気ですか？日はいいですね。\
                        私たちが生きだって嬉しいではないか？\r\n\
                        Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?\r\n\
                        こんにちは！元気ですか？日はいいですね。\
                        私たちが生きだって嬉しいではないか？\r\n\
                        Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?\r\n\
                        こんにちは！元気ですか？日はいいですね。\
                        私たちが生きだって嬉しいではないか？\r\n\
                        Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?\r\n\
                        こんにちは！元気ですか？日はいいですね。\
                        私たちが生きだって嬉しいではないか？\r\n\
                        ";

    #[test]
    fn bytes_01() {
        let r = Rope::from_str(TEXT);
        for (br, bt) in r.bytes().zip(TEXT.bytes()) {
            assert_eq!(br, bt);
        }
    }

    #[test]
    fn chars_01() {
        let r = Rope::from_str(TEXT);
        for (cr, ct) in r.chars().zip(TEXT.chars()) {
            assert_eq!(cr, ct);
        }
    }

    #[test]
    fn lines_01() {
        let r = Rope::from_str(TEXT);
        let s = r.slice(..);

        assert_eq!(33, r.lines().count());
        assert_eq!(33, s.lines().count());

        // Rope
        let mut lines = r.lines();
        assert_eq!("\r\n", lines.next().unwrap());
        for _ in 0..16 {
            assert_eq!(
                "Hello there!  How're you doing?  It's a fine day, \
                 isn't it?  Aren't you glad we're alive?\r\n",
                lines.next().unwrap()
            );
            assert_eq!(
                "こんにちは！元気ですか？日はいいですね。\
                 私たちが生きだって嬉しいではないか？\r\n",
                lines.next().unwrap()
            );
        }
        assert!(lines.next().is_none());

        // Slice
        let mut lines = s.lines();
        assert_eq!("\r\n", lines.next().unwrap());
        for _ in 0..16 {
            assert_eq!(
                "Hello there!  How're you doing?  It's a fine day, \
                 isn't it?  Aren't you glad we're alive?\r\n",
                lines.next().unwrap()
            );
            assert_eq!(
                "こんにちは！元気ですか？日はいいですね。\
                 私たちが生きだって嬉しいではないか？\r\n",
                lines.next().unwrap()
            );
        }
        assert!(lines.next().is_none());
    }

    #[test]
    fn lines_02() {
        let text = "Hello there!\nHow goes it?";
        let r = Rope::from_str(text);
        let s = r.slice(..);

        assert_eq!(2, r.lines().count());
        assert_eq!(2, s.lines().count());

        let mut lines = r.lines();
        assert_eq!("Hello there!\n", lines.next().unwrap());
        assert_eq!("How goes it?", lines.next().unwrap());
        assert!(lines.next().is_none());

        let mut lines = s.lines();
        assert_eq!("Hello there!\n", lines.next().unwrap());
        assert_eq!("How goes it?", lines.next().unwrap());
        assert!(lines.next().is_none());
    }

    #[test]
    fn lines_03() {
        let text = "Hello there!\nHow goes it?\n";
        let r = Rope::from_str(text);
        let s = r.slice(..);

        assert_eq!(2, r.lines().count());
        assert_eq!(2, s.lines().count());

        let mut lines = r.lines();
        assert_eq!("Hello there!\n", lines.next().unwrap());
        assert_eq!("How goes it?\n", lines.next().unwrap());
        assert!(lines.next().is_none());

        let mut lines = s.lines();
        assert_eq!("Hello there!\n", lines.next().unwrap());
        assert_eq!("How goes it?\n", lines.next().unwrap());
        assert!(lines.next().is_none());
    }

    #[test]
    fn lines_04() {
        let text = "Hello there!\nHow goes it?\nYeah!";
        let r = Rope::from_str(text);
        let s1 = r.slice(..25);
        let s2 = r.slice(..26);

        assert_eq!(2, s1.lines().count());
        assert_eq!(2, s2.lines().count());

        let mut lines = s1.lines();
        assert_eq!("Hello there!\n", lines.next().unwrap());
        assert_eq!("How goes it?", lines.next().unwrap());
        assert!(lines.next().is_none());

        let mut lines = s2.lines();
        assert_eq!("Hello there!\n", lines.next().unwrap());
        assert_eq!("How goes it?\n", lines.next().unwrap());
        assert!(lines.next().is_none());
    }

    #[test]
    fn lines_05() {
        let text = "";
        let r = Rope::from_str(text);
        let s = r.slice(..);

        assert_eq!(0, r.lines().count());
        assert_eq!(0, s.lines().count());

        let mut lines = r.lines();
        assert!(lines.next().is_none());

        let mut lines = s.lines();
        assert!(lines.next().is_none());
    }

    #[test]
    fn lines_06() {
        let text = "a";
        let r = Rope::from_str(text);
        let s = r.slice(..);

        assert_eq!(1, r.lines().count());
        assert_eq!(1, s.lines().count());

        let mut lines = r.lines();
        assert_eq!("a", lines.next().unwrap());
        assert!(lines.next().is_none());

        let mut lines = s.lines();
        assert_eq!("a", lines.next().unwrap());
        assert!(lines.next().is_none());
    }

    #[test]
    fn lines_07() {
        let text = "a\nb";
        let r = Rope::from_str(text);
        let s = r.slice(..);

        assert_eq!(2, r.lines().count());
        assert_eq!(2, s.lines().count());

        let mut lines = r.lines();
        assert_eq!("a\n", lines.next().unwrap());
        assert_eq!("b", lines.next().unwrap());
        assert!(lines.next().is_none());

        let mut lines = s.lines();
        assert_eq!("a\n", lines.next().unwrap());
        assert_eq!("b", lines.next().unwrap());
        assert!(lines.next().is_none());
    }

    #[test]
    fn lines_08() {
        let text = "\n";
        let r = Rope::from_str(text);
        let s = r.slice(..);

        assert_eq!(1, r.lines().count());
        assert_eq!(1, s.lines().count());

        let mut lines = r.lines();
        assert_eq!("\n", lines.next().unwrap());
        assert!(lines.next().is_none());

        let mut lines = s.lines();
        assert_eq!("\n", lines.next().unwrap());
        assert!(lines.next().is_none());
    }

    #[test]
    fn lines_09() {
        let text = "a\nb\n";
        let r = Rope::from_str(text);
        let s = r.slice(..);

        assert_eq!(2, r.lines().count());
        assert_eq!(2, s.lines().count());

        let mut lines = r.lines();
        assert_eq!("a\n", lines.next().unwrap());
        assert_eq!("b\n", lines.next().unwrap());
        assert!(lines.next().is_none());

        let mut lines = s.lines();
        assert_eq!("a\n", lines.next().unwrap());
        assert_eq!("b\n", lines.next().unwrap());
        assert!(lines.next().is_none());
    }

    #[test]
    fn lines_10() {
        let eq = |text: &str| {
            let forward: Vec<&str> = text.lines().collect();
            let mut reverse: Vec<&str> = text.lines().rev().collect();
            reverse.reverse();
            assert_eq!(forward, reverse);
        };

        eq(TEXT);
        eq("");
        eq("\n");
        eq("\n \r\n");
        eq("\u{000A}");
        eq("\u{000B}");
        eq("\u{000C}");
        eq("\u{000D}");
        eq("\u{0085}");
        eq("\u{2028}");
        eq("\u{2029}");
    }

    #[test]
    fn double_ended_lines_01() {
        let mut switch = true;
        let mut lines = TEXT.lines();
        let mut next = |front: &mut Vec<&str>, back: &mut Vec<&str>| {
            switch = !switch;
            if switch {
                lines.next().map(|l| front.push(l))
            } else {
                lines.next_back().map(|l| back.push(l))
            }
        };

        let mut front = vec![];
        let mut back: Vec<&str> = vec![];
        while let Some(_) = next(&mut front, &mut back) {}
        back.reverse();
        front.append(&mut back);

        let forward: Vec<&str> = TEXT.lines().collect();
        assert_eq!(forward, front);
    }

    fn collect<I: ExactSizeIterator + Clone, U: Debug + Eq>(
        iter: I,
        next: fn(&mut I) -> Option<U>,
    ) -> Vec<U> {
        let n = iter.clone().len();
        let mut m_iter = iter.clone();
        let mut vec = Vec::with_capacity(n);

        for i in 0..n {
            let len = m_iter.clone().len();
            let rs = next(&mut m_iter).unwrap_or_else(|| {
                panic!(
                    "Expected Iterator to hold {} items. Iterator returned None at {}",
                    n, i
                )
            });

            assert_eq!(len - 1, m_iter.clone().len());

            vec.push(rs);
        }
        assert_eq!(None, next(&mut m_iter));
        assert_eq!(None, next(&mut m_iter));

        vec
    }

    fn reverse<U>(vec: Vec<U>) -> Vec<U> {
        vec.into_iter().rev().collect()
    }

    #[test]
    /// Check Lines Iterator is the same forward and backwards.
    fn double_ended_lines_02() {
        let light = Lines::from(TEXT);
        let full = Rope::from_str(TEXT);
        let full = full.lines();

        let lf = collect(light.clone(), Iterator::next);
        let lb = reverse(collect(light, DoubleEndedIterator::next_back));

        let ff = collect(full.clone(), Iterator::next);
        let fb = reverse(collect(full, DoubleEndedIterator::next_back));

        assert_eq!(lf, lb);
        assert_eq!(ff, fb);
        assert_eq!(ff, lf);
    }

    #[test]
    /// Text without trailing line-break.
    fn double_ended_lines_03() {
        let text = &TEXT[..TEXT.len() - 2];
        let light = Lines::from(text);
        let full = Rope::from_str(text);
        let full = full.lines();

        let lf = collect(light.clone(), Iterator::next);
        let lb = reverse(collect(light, DoubleEndedIterator::next_back));

        let ff = collect(full.clone(), Iterator::next);
        let fb = reverse(collect(full, DoubleEndedIterator::next_back));

        assert_eq!(lf, lb);
        assert_eq!(ff, fb);
        assert_eq!(ff, lf);
    }

    #[test]
    fn lines_size_hint_01() {
        let light = Lines::from(TEXT);
        let full = Rope::from_str(TEXT);

        assert!(full.lines().size_hint().0 >= full.lines().len());

        assert_eq!(light.size_hint(), full.lines().size_hint());
        assert_eq!(light.len(), light.size_hint().0);
    }

    #[test]
    fn exact_lines_len_01() {
        let full = Rope::from_str(TEXT);
        let light = Lines::from(TEXT);
        assert_eq!(full.lines().count(), full.lines().len());
        assert_eq!(full.lines().count(), light.clone().count());
        assert_eq!(light.clone().count(), light.clone().len());

        collect(light, Iterator::next);
        collect(full.lines(), Iterator::next);
    }

    #[test]
    fn exact_lines_len_02() {
        let text = &TEXT[..TEXT.len() - 2];
        let full = Rope::from_str(text);
        let light = Lines::from(text);
        assert_eq!(full.lines().count(), full.lines().len());
        assert_eq!(full.lines().count(), light.clone().count());
        assert_eq!(light.clone().count(), light.clone().len());

        collect(light, Iterator::next);
        collect(full.lines(), Iterator::next);
    }

    #[test]
    fn narrow_lines_01() {
        let light = Lines::from(TEXT);
        let full = Rope::from_str(TEXT);
        let full = full.lines();

        let nf = full.clone().narrow(0..full.clone().len());
        let nl = light.clone().narrow(0..light.clone().len());
        // After `light.len()` narrow knows the line break count.
        let nll = light.clone().narrow(0..light.len());

        let l = light;
        let f = full.clone();
        assert_eq!(f, l);
        assert_eq!(f, nl);
        assert_eq!(f, nll);
        assert_eq!(f, nf);
    }

    #[test]
    fn narrow_lines_02() {
        let light = Lines::from(TEXT);
        let full = Rope::from_str(TEXT);
        let full = full.lines();

        let f = full.clone().skip(2).take(2);
        let l = light.clone().skip(2).take(2);

        assert_eq!(f.clone().next(), l.clone().next());

        let nf = full.clone().narrow(2..4);
        let nl = light.clone().narrow(2..4);
        assert_eq!(nf, nl);
        assert_eq!(
            f.clone().collect::<Vec<_>>(),
            nl.clone().collect::<Vec<_>>()
        );

        let nl = nl.clone().narrow(0..3);
        let nf = nf.clone().narrow(0..3);
        assert_eq!(nf, nl);
        assert_eq!(
            f.clone().collect::<Vec<_>>(),
            nl.clone().collect::<Vec<_>>()
        );
    }

    #[test]
    fn lines_into_ropeslice_01() {
        let r = Rope::from(TEXT);
        let rs = RopeSlice::from(r.lines());
        assert_eq!(r.slice(..), rs);

        let mut rs = r.lines();
        rs.nth(1);
        let rs = RopeSlice::from(rs).lines();
        assert_eq!(rs, r.lines().narrow(2..r.lines().len()));

        let mut rs = r.lines();
        rs.next_back();
        let rs = RopeSlice::from(rs).lines();
        assert_eq!(rs, r.lines().narrow(0..rs.len()));

        let rs = RopeSlice::from(r.lines().narrow(3..6)).lines();
        assert_eq!(rs, r.lines().narrow(3..6));
    }

    #[test]
    fn chunks_01() {
        let r = Rope::from_str(TEXT);

        let mut idx = 0;
        for chunk in r.chunks() {
            assert_eq!(chunk, &TEXT[idx..(idx + chunk.len())]);
            idx += chunk.len();
        }
    }

    #[test]
    fn bytes_sliced_01() {
        let r = Rope::from_str(TEXT);

        let s_start = 116;
        let s_end = 331;
        let s_start_byte = r.char_to_byte(s_start);
        let s_end_byte = r.char_to_byte(s_end);

        let s1 = r.slice(s_start..s_end);
        let s2 = &TEXT[s_start_byte..s_end_byte];

        for (br, bt) in s1.bytes().zip(s2.bytes()) {
            assert_eq!(br, bt);
        }
    }

    #[test]
    fn chars_sliced_01() {
        let r = Rope::from_str(TEXT);

        let s_start = 116;
        let s_end = 331;
        let s_start_byte = r.char_to_byte(s_start);
        let s_end_byte = r.char_to_byte(s_end);

        let s1 = r.slice(s_start..s_end);
        let s2 = &TEXT[s_start_byte..s_end_byte];

        for (cr, ct) in s1.chars().zip(s2.chars()) {
            assert_eq!(cr, ct);
        }
    }

    #[test]
    fn lines_sliced_01() {
        let r = Rope::from_str(TEXT);

        let s_start = 116;
        let s_end = 331;
        let s_start_byte = r.char_to_byte(s_start);
        let s_end_byte = r.char_to_byte(s_end);

        let s1 = r.slice(s_start..s_end);
        let s2 = &TEXT[s_start_byte..s_end_byte];

        for (liner, linet) in s1.lines().zip(s2.lines()) {
            assert_eq!(liner.to_string().trim_end(), linet);
        }
    }

    #[test]
    fn chunks_sliced_01() {
        let r = Rope::from_str(TEXT);

        let s_start = 116;
        let s_end = 331;
        let s_start_byte = r.char_to_byte(s_start);
        let s_end_byte = r.char_to_byte(s_end);

        let s1 = r.slice(s_start..s_end);
        let s2 = &TEXT[s_start_byte..s_end_byte];

        let mut idx = 0;
        for chunk in s1.chunks() {
            assert_eq!(chunk, &s2[idx..(idx + chunk.len())]);
            idx += chunk.len();
        }
    }
}
