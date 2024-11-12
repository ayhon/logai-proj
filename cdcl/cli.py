"""This module implements a client to use CDCL"""
# cdcl/cli.py

from typing import Annotated

from itertools import zip_longest

from pathlib import Path

import typer

from cdcl import cdcl, __app_name__, __version__

app = typer.Typer()


@app.command()
def sat(
    formula_files: Annotated[list[str], typer.Argument(
        help="Files containing formulas in DIMACS format"
    )],
    output_files: Annotated[list[str], typer.Option(
        "--output",
        "-o",
        help="Files to store the outputs."
    )] = [None],
    fuel: Annotated[int, typer.Option(
        "--fuel",
        "-f",
        help="Maximum number of iterations"
    )] = cdcl.DEFAULT_RECURSION_FUEL,
    verbose: Annotated[bool, typer.Option(
        "--verbose",
        "-v",
        help=""
    )] = False
):
    "Find a satisfying model for a CNF formula, if one exists."
    if len(output_files) == 1:
        output_files *= len(formula_files)
    for ff, of in zip_longest(formula_files, output_files):
        source_file = Path(ff)
        formula = cdcl.read_dimacs(source_file)
        model = cdcl.get_model(formula, fuel=fuel)
        if of is not None:
            output_file = Path(of)
            with output_file.open("w", encoding="ascii") as f:
                f.write(str(model))
        if verbose:
            print(f"{ff}", model)


@app.command()
def check(
    models: Annotated[list[str], typer.Argument(
        help="File listing assignment for each variable"
    )],
    formula: Annotated[str, typer.Option(
        "--formula",
        "-f",
        help="A formula to check"
    )]
):
    "Check that a model entails a formula."
    f = cdcl.read_dimacs(Path(formula))
    for model_path in models:
        model = cdcl.Model.from_file(Path(model_path))
        if model.entails(f) is True:
            print(f"✅ {model_path} entails the formula")
        elif model.entails(f) is False:
            print(f"❌ {model_path} doesn't entail the formula")
        else:
            print(f"❓ {model_path} doesn't assign the formula")


def _version_callback(value: bool) -> None:
    if value:
        typer.echo(f"{__app_name__} v{__version__}")
        raise typer.Exit()


@app.callback()
def main(
    version: bool | None = typer.Option(
        None,
        "--version",
        help="Show the application's version and exit.",
        callback=_version_callback,
        is_eager=True,
    )
) -> None:
    return
