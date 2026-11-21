import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0171 : checkSingleBlackFast (-5, 8) 4841 .east (0, -8) (-16, -17) = true := by
  decide +kernel

end LangtonsAnt
