import Problib.Measure.Convergence
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.farEvent,
  Problib.Measure.ConvergesInProbability,
  Problib.Measure.convergesInProbability_map₂,
  Problib.Measure.convergesInProbability_div,
  Problib.Measure.convergesInProbability_of_meanSquare
]

#audit_registered_claims

#audit_package [Problib.Measure.Convergence] allowing [propext, Quot.sound, Classical.choice]
