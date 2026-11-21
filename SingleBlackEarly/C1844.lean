import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1844 : checkSingleBlackFast (-59, -34) 20855 .east (32, 11) (-14, -50) = true := by
  decide +kernel

end LangtonsAnt
