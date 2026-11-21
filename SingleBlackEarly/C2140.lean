import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2140 : checkSingleBlackFast (-86, -65) 20965 .east (34, 24) (18, -57) = true := by
  decide +kernel

end LangtonsAnt
