import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1865 : checkSingleBlackFast (-63, -35) 24905 .east (27, 15) (5, -50) = true := by
  decide +kernel

end LangtonsAnt
