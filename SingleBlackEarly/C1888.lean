import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1888 : checkSingleBlackFast (-63, -38) 21063 .east (34, 13) (-12, -52) = true := by
  decide +kernel

end LangtonsAnt
