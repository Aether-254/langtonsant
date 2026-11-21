import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1734 : checkSingleBlackFast (-49, -24) 20335 .east (27, 6) (-19, -45) = true := by
  decide +kernel

end LangtonsAnt
