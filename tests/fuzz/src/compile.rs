#![no_main]

use libfuzzer_sys::fuzz_target;
use freepst::diag::{FileError, FileResult};
use freepst::foundations::{Bytes, Datetime};
use freepst::layout::PagedDocument;
use freepst::syntax::{FileId, Source};
use freepst::text::{Font, FontBook};
use freepst::utils::LazyHash;
use freepst::{Library, World};

struct FuzzWorld {
    library: LazyHash<Library>,
    book: LazyHash<FontBook>,
    font: Font,
    source: Source,
}

impl FuzzWorld {
    fn new(text: &str) -> Self {
        let data = freepst_assets::fonts().next().unwrap();
        let font = Font::new(Bytes::from_static(data), 0).unwrap();
        let book = FontBook::from_fonts([&font]);
        Self {
            library: LazyHash::new(Library::default()),
            book: LazyHash::new(book),
            font,
            source: Source::detached(text),
        }
    }
}

impl World for FuzzWorld {
    fn library(&self) -> &LazyHash<Library> {
        &self.library
    }

    fn book(&self) -> &LazyHash<FontBook> {
        &self.book
    }

    fn main(&self) -> FileId {
        self.source.id()
    }

    fn source(&self, id: FileId) -> FileResult<Source> {
        if id == self.source.id() {
            Ok(self.source.clone())
        } else {
            Err(FileError::NotFound(id.vpath().as_rootless_path().into()))
        }
    }

    fn file(&self, id: FileId) -> FileResult<Bytes> {
        Err(FileError::NotFound(id.vpath().as_rootless_path().into()))
    }

    fn font(&self, _: usize) -> Option<Font> {
        Some(self.font.clone())
    }

    fn today(&self, _: Option<i64>) -> Option<Datetime> {
        None
    }
}

fuzz_target!(|text: &str| {
    let world = FuzzWorld::new(text);
    if let Ok(document) = freepst::compile::<PagedDocument>(&world).output {
        if let Some(page) = document.pages.first() {
            std::hint::black_box(freepst_render::render(page, 1.0));
        }
    }
    comemo::evict(10);
});
