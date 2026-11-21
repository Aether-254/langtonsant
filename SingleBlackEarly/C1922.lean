import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1922 : checkSingleBlackFast (-64, -46) 28771 .east (35, 23) (-6, -45) = true := by
  decide +kernel

end LangtonsAnt
