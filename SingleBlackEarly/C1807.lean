import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1807 : checkSingleBlackFast (-57, -33) 14263 .west (15, 26) (-45, 7) = true := by
  decide +kernel

end LangtonsAnt
