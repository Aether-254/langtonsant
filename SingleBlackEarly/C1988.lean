import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1988 : checkSingleBlackFast (-70, -52) 29083 .east (38, 26) (-3, -48) = true := by
  decide +kernel

end LangtonsAnt
