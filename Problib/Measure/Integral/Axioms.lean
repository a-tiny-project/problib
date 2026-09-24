import Problib.Measure.Integral
import Problib.Measure.Integral.Density.Axioms
import Problib.Measure.Integral.Lebesgue.Axioms
import Problib.Measure.Integral.Simple.Axioms
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.IntegralParts.smulNonnegative,
  Problib.Measure.IntegralParts.smulNonnegative_value,
  Problib.Measure.IntegralParts.negParts,
  Problib.Measure.IntegralParts.negParts_value,
  Problib.Measure.IntegralParts.smul,
  Problib.Measure.IntegralParts.smul_value,
  Problib.Measure.IntegralParts.unique,
  Problib.Measure.IntegralParts.scalar_decomposition,
  Problib.Measure.IntegralParts.const,
  Problib.Measure.IntegralParts.const_value,
  Problib.Measure.IntegralParts.addParts,
  Problib.Measure.IntegralParts.addParts_value,
  Problib.Measure.IntegralParts.congr,
  Problib.Measure.IntegralParts.congr_value,
  Problib.Measure.HasRealIntegral.unique,
  Problib.Measure.IntegralParts.measurable,
  Problib.Measure.IntegralParts.canonical,
  Problib.Measure.HasRealIntegral.congr,
  Problib.Measure.HasRealIntegral.add,
  Problib.Measure.HasRealIntegral.neg,
  Problib.Measure.HasRealIntegral.sub,
  Problib.Measure.HasRealIntegral.smul,
  Problib.Measure.IntegralParts.comap,
  Problib.Measure.IntegralParts.comap_value,
  Problib.Measure.HasRealIntegral.map,
  Problib.Measure.smul_hasRealIntegral,
  Problib.Measure.hasRealIntegral_of_bounded,
  Problib.Measure.HasRealIntegral.lintegral_ofReal,
  Problib.Measure.layerCake_measurable,
  Problib.Measure.lintegral_layerCake_fiber,
  Problib.Measure.lintegral_layer_cake,
  Problib.Measure.lintegral_layer_cake_one,
  Problib.Measure.layer_cake_requires_zero_cutoff
]

#audit_registered_claims

#audit_package [Problib.Measure.Integral] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
