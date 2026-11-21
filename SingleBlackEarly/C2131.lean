import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2131 : checkSingleBlackFast (-86, -61) 19267 .east (31, 34) (9, -51) = true := by
  decide +kernel

end LangtonsAnt
