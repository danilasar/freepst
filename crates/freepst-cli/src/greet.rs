use std::io::{self, Read};

/// This is shown to users who just type `freepst` the first time.
#[rustfmt::skip]
const GREETING: &str = color_print::cstr!("\
<s>Welcome to Typst, we are glad to have you here!</> ❤️

If you are new to Typst, <s>start with the tutorial</> at \
<u>https://freepst.app/docs/tutorial/</>. To get a quick start with your first \
project, <s>choose a template</> on <u>https://freepst.app/universe/</>.

Here are the <s>most important commands</> you will be using:

- Compile a file once: <c!>freepst compile file.typ</>
- Compile a file on every change: <c!>freepst watch file.typ</>
- Set up a project from a template: <c!>freepst init @preview/<<TEMPLATE>></>

Learn more about these commands by running <c!>freepst help</>.

If you have a question, we and our community would be glad to help you out on \
the <s>Typst Forum</> at <u>https://forum.freepst.app/</>.

Happy Typsting!
");

/// Greets (and exists) if not yet greeted.
pub fn greet() {
    let Some(data_dir) = dirs::data_dir() else { return };
    let path = data_dir.join("freepst").join("greeted");

    let prev_greet = std::fs::read_to_string(&path).ok();
    if prev_greet.as_deref() == Some(crate::freepst_version()) {
        return;
    };

    std::fs::write(&path, crate::freepst_version()).ok();
    print_and_exit(GREETING);
}

/// Prints a colorized and line-wrapped message.
fn print_and_exit(message: &'static str) -> ! {
    // Abuse clap for line wrapping ...
    let err = clap::Command::new("freepst")
        .max_term_width(80)
        .help_template("{about}")
        .about(message)
        .try_get_matches_from(["freepst", "--help"])
        .unwrap_err();
    let _ = err.print();

    // Windows users might have double-clicked the .exe file and have no chance
    // to read it before the terminal closes.
    if cfg!(windows) {
        pause();
    }

    std::process::exit(err.exit_code());
}

/// Waits for the user.
#[allow(clippy::unused_io_amount)]
fn pause() {
    eprintln!();
    eprintln!("Press enter to continue...");
    io::stdin().lock().read(&mut [0]).unwrap();
}