import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1806 : checkSingleBlackFast (-57, -34) 19437 .east (26, 11) (3, -45) = true := by
  decide +kernel

end LangtonsAnt
