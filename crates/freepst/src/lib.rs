//! The compiler for the _Typst_ markup language.
//!
//! # Steps
//! - **Parsing:**
//!   The compiler first transforms a plain string into an iterator of [tokens].
//!   This token stream is [parsed] into a [syntax tree]. The tree itself is
//!   untyped, but the [AST] module provides a typed layer over it.
//! - **Evaluation:**
//!   The next step is to [evaluate] the markup. This produces a [module],
//!   consisting of a scope of values that were exported by the code and
//!   [content], a hierarchical, styled representation of what was written in
//!   the source file. The elements of the content tree are well structured and
//!   order-independent and thus much better suited for further processing than
//!   the raw markup.
//! - **Layouting:**
//!   Next, the content is [laid out] into a [`PagedDocument`] containing one
//!   [frame] per page with items at fixed positions.
//! - **Exporting:**
//!   These frames can finally be exported into an output format (currently PDF,
//!   PNG, SVG, and HTML).
//!
//! [tokens]: typst_syntax::SyntaxKind
//! [parsed]: typst_syntax::parse
//! [syntax tree]: typst_syntax::SyntaxNode
//! [AST]: typst_syntax::ast
//! [evaluate]: typst_eval::eval
//! [module]: crate::foundations::Module
//! [content]: crate::foundations::Content
//! [laid out]: typst_layout::layout_document
//! [document]: crate::model::Document
//! [frame]: crate::layout::Frame

pub extern crate comemo;
pub extern crate ecow;

pub use typst_library::*;
#[doc(inline)]
pub use typst_syntax as syntax;
#[doc(inline)]
pub use typst_utils as utils;

use std::collections::HashSet;

use comemo::{Track, Tracked, Validate};
use ecow::{eco_format, eco_vec, EcoString, EcoVec};
use typst_library::diag::{
    bail, warning, FileError, SourceDiagnostic, SourceResult, Warned,
};
use typst_library::engine::{Engine, Route, Sink, Traced};
use typst_library::foundations::{StyleChain, Styles, Value};
use typst_library::html::HtmlDocument;
use typst_library::introspection::Introspector;
use typst_library::layout::PagedDocument;
use typst_library::routines::Routines;
use typst_syntax::{FileId, Span};
use typst_timing::{timed, TimingScope};

use crate::foundations::{Target, TargetElem};
use crate::model::DocumentInfo;

/// Compile sources into a fully layouted document.
///
/// - Returns `Ok(document)` if there were no fatal errors.
/// - Returns `Err(errors)` if there were fatal errors.
#[typst_macros::time]
pub fn compile<D>(world: &dyn World) -> Warned<SourceResult<D>>
where
    D: Document,
{
    let mut sink = Sink::new();
    let output = compile_impl::<D>(world.track(), Traced::default().track(), &mut sink)
        .map_err(deduplicate);
    Warned { output, warnings: sink.warnings() }
}

/// Compiles sources and returns all values and styles observed at the given
/// `span` during compilation.
#[typst_macros::time]
pub fn trace<D>(world: &dyn World, span: Span) -> EcoVec<(Value, Option<Styles>)>
where
    D: Document,
{
    let mut sink = Sink::new();
    let traced = Traced::new(span);
    compile_impl::<D>(world.track(), traced.track(), &mut sink).ok();
    sink.values()
}

/// The internal implementation of `compile` with a bit lower-level interface
/// that is also used by `trace`.
fn compile_impl<D: Document>(
    world: Tracked<dyn World + '_>,
    traced: Tracked<Traced>,
    sink: &mut Sink,
) -> SourceResult<D> {
    if D::TARGET == Target::Html {
        warn_or_error_for_html(world, sink)?;
    }

    let library = world.library();
    let base = StyleChain::new(&library.styles);
    let target = TargetElem::set_target(D::TARGET).wrap();
    let styles = base.chain(&target);
    let empty_introspector = Introspector::default();

    // Fetch the main source file once.
    let main = world.main();
    let main = world
        .source(main)
        .map_err(|err| hint_invalid_main_file(world, err, main))?;

    // First evaluate the main source file into a module.
    let content = typst_eval::eval(
        &ROUTINES,
        world,
        traced,
        sink.track_mut(),
        Route::default().track(),
        &main,
    )?
    .content();

    let mut iter = 0;
    let mut subsink;
    let mut introspector = &empty_introspector;
    let mut document: D;

    // Relayout until all introspections stabilize.
    // If that doesn't happen within five attempts, we give up.
    loop {
        // The name of the iterations for timing scopes.
        const ITER_NAMES: &[&str] =
            &["layout (1)", "layout (2)", "layout (3)", "layout (4)", "layout (5)"];
        let _scope = TimingScope::new(ITER_NAMES[iter]);

        subsink = Sink::new();

        let constraint = <Introspector as Validate>::Constraint::new();
        let mut engine = Engine {
            world,
            introspector: introspector.track_with(&constraint),
            traced,
            sink: subsink.track_mut(),
            route: Route::default(),
            routines: &ROUTINES,
        };

        // Layout!
        document = D::create(&mut engine, &content, styles)?;
        introspector = document.introspector();
        iter += 1;

        if timed!("check stabilized", introspector.validate(&constraint)) {
            break;
        }

        if iter >= 5 {
            subsink.warn(warning!(
                Span::detached(), "layout did not converge within 5 attempts";
                hint: "check if any states or queries are updating themselves"
            ));
            break;
        }
    }

    sink.extend_from_sink(subsink);

    // Promote delayed errors.
    let delayed = sink.delayed();
    if !delayed.is_empty() {
        return Err(delayed);
    }

    Ok(document)
}

/// Deduplicate diagnostics.
fn deduplicate(mut diags: EcoVec<SourceDiagnostic>) -> EcoVec<SourceDiagnostic> {
    let mut unique = HashSet::new();
    diags.retain(|diag| {
        let hash = typst_utils::hash128(&(&diag.span, &diag.message));
        unique.insert(hash)
    });
    diags
}

<<<<<<< HEAD:crates/typst/src/lib.rs
=======
/// The environment in which typesetting occurs.
///
/// All loading functions (`main`, `source`, `file`, `font`) should perform
/// internal caching so that they are relatively cheap on repeated invocations
/// with the same argument. [`Source`], [`Bytes`], and [`Font`] are
/// all reference-counted and thus cheap to clone.
///
/// The compiler doesn't do the caching itself because the world has much more
/// information on when something can change. For example, fonts typically don't
/// change and can thus even be cached across multiple compilations (for
/// long-running applications like `freepst watch`). Source files on the other
/// hand can change and should thus be cleared after each compilation. Advanced
/// clients like language servers can also retain the source files and
/// [edit](Source::edit) them in-place to benefit from better incremental
/// performance.
#[comemo::track]
pub trait World: Send + Sync {
    /// The standard library.
    ///
    /// Can be created through `Library::build()`.
    fn library(&self) -> &LazyHash<Library>;

    /// Metadata about all known fonts.
    fn book(&self) -> &LazyHash<FontBook>;

    /// Get the file id of the main source file.
    fn main(&self) -> FileId;

    /// Try to access the specified source file.
    fn source(&self, id: FileId) -> FileResult<Source>;

    /// Try to access the specified file.
    fn file(&self, id: FileId) -> FileResult<Bytes>;

    /// Try to access the font with the given index in the font book.
    fn font(&self, index: usize) -> Option<Font>;

    /// Get the current date.
    ///
    /// If no offset is specified, the local date should be chosen. Otherwise,
    /// the UTC date should be chosen with the corresponding offset in hours.
    ///
    /// If this function returns `None`, Typst's `datetime` function will
    /// return an error.
    fn today(&self, offset: Option<i64>) -> Option<Datetime>;

    /// A list of all available packages and optionally descriptions for them.
    ///
    /// This function is optional to implement. It enhances the user experience
    /// by enabling autocompletion for packages. Details about packages from the
    /// `@preview` namespace are available from
    /// `https://packages.typst.org/preview/index.json`.
    fn packages(&self) -> &[(PackageSpec, Option<EcoString>)] {
        &[]
    }
}

macro_rules! delegate_for_ptr {
    ($W:ident for $ptr:ty) => {
        impl<$W: World> World for $ptr {
            fn library(&self) -> &LazyHash<Library> {
                self.deref().library()
            }

            fn book(&self) -> &LazyHash<FontBook> {
                self.deref().book()
            }

            fn main(&self) -> FileId {
                self.deref().main()
            }

            fn source(&self, id: FileId) -> FileResult<Source> {
                self.deref().source(id)
            }

            fn file(&self, id: FileId) -> FileResult<Bytes> {
                self.deref().file(id)
            }

            fn font(&self, index: usize) -> Option<Font> {
                self.deref().font(index)
            }

            fn today(&self, offset: Option<i64>) -> Option<Datetime> {
                self.deref().today(offset)
            }

            fn packages(&self) -> &[(PackageSpec, Option<EcoString>)] {
                self.deref().packages()
            }
        }
    };
}

delegate_for_ptr!(W for std::boxed::Box<W>);
delegate_for_ptr!(W for std::sync::Arc<W>);
delegate_for_ptr!(W for &W);

/// Helper methods on [`World`] implementations.
pub trait WorldExt {
    /// Get the byte range for a span.
    ///
    /// Returns `None` if the `Span` does not point into any source file.
    fn range(&self, span: Span) -> Option<Range<usize>>;
}

impl<T: World> WorldExt for T {
    fn range(&self, span: Span) -> Option<Range<usize>> {
        self.source(span.id()?).ok()?.range(span)
    }
}

/// Definition of Typst's standard library.
#[derive(Debug, Clone, Hash)]
pub struct Library {
    /// The module that contains the definitions that are available everywhere.
    pub global: Module,
    /// The module that contains the definitions available in math mode.
    pub math: Module,
    /// The default style properties (for page size, font selection, and
    /// everything else configurable via set and show rules).
    pub styles: Styles,
    /// The standard library as a value.
    /// Used to provide the `std` variable.
    pub std: Value,
}

impl Library {
    /// Create a new builder for a library.
    pub fn builder() -> LibraryBuilder {
        LibraryBuilder::default()
    }
}

impl Default for Library {
    /// Constructs the standard library with the default configuration.
    fn default() -> Self {
        Self::builder().build()
    }
}

/// Configurable builder for the standard library.
///
/// This struct is created by [`Library::builder`].
#[derive(Debug, Clone, Default)]
pub struct LibraryBuilder {
    inputs: Option<Dict>,
}

impl LibraryBuilder {
    /// Configure the inputs visible through `sys.inputs`.
    pub fn with_inputs(mut self, inputs: Dict) -> Self {
        self.inputs = Some(inputs);
        self
    }

    /// Consumes the builder and returns a `Library`.
    pub fn build(self) -> Library {
        let math = math::module();
        let inputs = self.inputs.unwrap_or_default();
        let global = global(math.clone(), inputs);
        let std = Value::Module(global.clone());
        Library { global, math, styles: Styles::new(), std }
    }
}

/// Construct the module with global definitions.
fn global(math: Module, inputs: Dict) -> Module {
    let mut global = Scope::deduplicating();
    self::foundations::define(&mut global, inputs);
    self::model::define(&mut global);
    self::text::define(&mut global);
    global.reset_category();
    global.define_module(math);
    self::layout::define(&mut global);
    self::visualize::define(&mut global);
    self::introspection::define(&mut global);
    self::loading::define(&mut global);
    self::symbols::define(&mut global);
    prelude(&mut global);
    Module::new("global", global)
}

/// Defines scoped values that are globally available, too.
fn prelude(global: &mut Scope) {
    global.reset_category();
    global.define("black", Color::BLACK);
    global.define("gray", Color::GRAY);
    global.define("silver", Color::SILVER);
    global.define("white", Color::WHITE);
    global.define("navy", Color::NAVY);
    global.define("blue", Color::BLUE);
    global.define("aqua", Color::AQUA);
    global.define("teal", Color::TEAL);
    global.define("eastern", Color::EASTERN);
    global.define("purple", Color::PURPLE);
    global.define("fuchsia", Color::FUCHSIA);
    global.define("maroon", Color::MAROON);
    global.define("red", Color::RED);
    global.define("orange", Color::ORANGE);
    global.define("yellow", Color::YELLOW);
    global.define("olive", Color::OLIVE);
    global.define("green", Color::GREEN);
    global.define("lime", Color::LIME);
    global.define("luma", Color::luma_data());
    global.define("oklab", Color::oklab_data());
    global.define("oklch", Color::oklch_data());
    global.define("rgb", Color::rgb_data());
    global.define("cmyk", Color::cmyk_data());
    global.define("range", Array::range_data());
    global.define("ltr", Dir::LTR);
    global.define("rtl", Dir::RTL);
    global.define("ttb", Dir::TTB);
    global.define("btt", Dir::BTT);
    global.define("start", Alignment::START);
    global.define("left", Alignment::LEFT);
    global.define("center", Alignment::CENTER);
    global.define("right", Alignment::RIGHT);
    global.define("end", Alignment::END);
    global.define("top", Alignment::TOP);
    global.define("horizon", Alignment::HORIZON);
    global.define("bottom", Alignment::BOTTOM);
}

>>>>>>> dbf12fc8 (Взлетаем):crates/freepst/src/lib.rs
/// Adds useful hints when the main source file couldn't be read
/// and returns the final diagnostic.
fn hint_invalid_main_file(
    world: Tracked<dyn World + '_>,
    file_error: FileError,
    input: FileId,
) -> EcoVec<SourceDiagnostic> {
    let is_utf8_error = matches!(file_error, FileError::InvalidUtf8);
    let mut diagnostic =
        SourceDiagnostic::error(Span::detached(), EcoString::from(file_error));

    // Attempt to provide helpful hints for UTF-8 errors. Perhaps the user
    // mistyped the filename. For example, they could have written "file.pdf"
    // instead of "file.typ".
    if is_utf8_error {
        let path = input.vpath();
        let extension = path.as_rootless_path().extension();
        if extension.is_some_and(|extension| extension == "typ") {
            // No hints if the file is already a .typ file.
            // The file is indeed just invalid.
            return eco_vec![diagnostic];
        }

        match extension {
            Some(extension) => {
                diagnostic.hint(eco_format!(
                    "a file with the `.{}` extension is not usually a Typst file",
                    extension.to_string_lossy()
                ));
            }

            None => {
                diagnostic
                    .hint("a file without an extension is not usually a Typst file");
            }
        };

        if world.source(input.with_extension("typ")).is_ok() {
            diagnostic.hint("check if you meant to use the `.typ` extension instead");
        }
    }

    eco_vec![diagnostic]
}

/// HTML export will warn or error depending on whether the feature flag is enabled.
fn warn_or_error_for_html(
    world: Tracked<dyn World + '_>,
    sink: &mut Sink,
) -> SourceResult<()> {
    const ISSUE: &str = "https://github.com/typst/typst/issues/5512";
    if world.library().features.is_enabled(Feature::Html) {
        sink.warn(warning!(
            Span::detached(),
            "html export is under active development and incomplete";
            hint: "its behaviour may change at any time";
            hint: "do not rely on this feature for production use cases";
            hint: "see {ISSUE} for more information"
        ));
    } else {
        bail!(
            Span::detached(),
            "html export is only available when `--features html` is passed";
            hint: "html export is under active development and incomplete";
            hint: "see {ISSUE} for more information"
        );
    }
    Ok(())
}

/// A document is what results from compilation.
pub trait Document: sealed::Sealed {
    /// Get the document's metadata.
    fn info(&self) -> &DocumentInfo;

    /// Get the document's introspector.
    fn introspector(&self) -> &Introspector;
}

impl Document for PagedDocument {
    fn info(&self) -> &DocumentInfo {
        &self.info
    }

    fn introspector(&self) -> &Introspector {
        &self.introspector
    }
}

impl Document for HtmlDocument {
    fn info(&self) -> &DocumentInfo {
        &self.info
    }

    fn introspector(&self) -> &Introspector {
        &self.introspector
    }
}

mod sealed {
    use typst_library::foundations::{Content, Target};

    use super::*;

    pub trait Sealed: Sized {
        const TARGET: Target;

        fn create(
            engine: &mut Engine,
            content: &Content,
            styles: StyleChain,
        ) -> SourceResult<Self>;
    }

    impl Sealed for PagedDocument {
        const TARGET: Target = Target::Paged;

        fn create(
            engine: &mut Engine,
            content: &Content,
            styles: StyleChain,
        ) -> SourceResult<Self> {
            typst_layout::layout_document(engine, content, styles)
        }
    }

    impl Sealed for HtmlDocument {
        const TARGET: Target = Target::Html;

        fn create(
            engine: &mut Engine,
            content: &Content,
            styles: StyleChain,
        ) -> SourceResult<Self> {
            typst_html::html_document(engine, content, styles)
        }
    }
}

/// Defines implementation of various Typst compiler routines as a table of
/// function pointers.
///
/// This is essentially dynamic linking and done to allow for crate splitting.
pub static ROUTINES: Routines = Routines {
    eval_string: typst_eval::eval_string,
    eval_closure: typst_eval::eval_closure,
    realize: typst_realize::realize,
    layout_fragment: typst_layout::layout_fragment,
    layout_frame: typst_layout::layout_frame,
    layout_inline: typst_layout::layout_inline,
    layout_box: typst_layout::layout_box,
    layout_list: typst_layout::layout_list,
    layout_enum: typst_layout::layout_enum,
    layout_grid: typst_layout::layout_grid,
    layout_table: typst_layout::layout_table,
    layout_stack: typst_layout::layout_stack,
    layout_columns: typst_layout::layout_columns,
    layout_move: typst_layout::layout_move,
    layout_rotate: typst_layout::layout_rotate,
    layout_scale: typst_layout::layout_scale,
    layout_skew: typst_layout::layout_skew,
    layout_repeat: typst_layout::layout_repeat,
    layout_pad: typst_layout::layout_pad,
    layout_line: typst_layout::layout_line,
    layout_curve: typst_layout::layout_curve,
    layout_path: typst_layout::layout_path,
    layout_polygon: typst_layout::layout_polygon,
    layout_rect: typst_layout::layout_rect,
    layout_square: typst_layout::layout_square,
    layout_ellipse: typst_layout::layout_ellipse,
    layout_circle: typst_layout::layout_circle,
    layout_image: typst_layout::layout_image,
    layout_equation_block: typst_layout::layout_equation_block,
    layout_equation_inline: typst_layout::layout_equation_inline,
};
