module

public import Submission.Improvement.Fields.ResidualDomain
public import Submission.CatalanMeasure.GenD.D58.Cert590.Data
public import Submission.CatalanMeasure.GenD.D58.Cert590.RTab
public import Submission.CatalanMeasure.GenD.D58.Cert590.RZ
public import Submission.CatalanMeasure.GenD.Cert.WLogSpec
public import Submission.CatalanMeasure.GenD.Cert.Assembly
public import Submission.CatalanMeasure.GenD.Analytic.Glue
public import Submission.CatalanMeasure.GenD.D58.OddProfile

@[expose] public section

namespace CatalanMeasure.Improvement.Fields

open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590

theorem trimmed_residual_spec_sound (t : ℕ) :
    (resSpecW (53 / 58 : ℚ) Pc P t).Sound D_R.toD
      (resFieldW ((53 / 58 : ℚ) : ℝ) (trialSeqS Pc P)) :=
  resSpecW_sound (53 / 58 : ℚ) tailsP P_nonzero D_R.toD hZ_R t

end CatalanMeasure.Improvement.Fields
